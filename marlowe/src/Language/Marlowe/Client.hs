{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module Language.Marlowe.Client where
import           Control.Lens
import           Control.Monad                                 (void)
import           Control.Monad.Error.Lens                      (catching, throwing)
import qualified Data.Map                                      as Map
import           Language.Marlowe.Semantics                    hiding (Contract)
import qualified Language.Marlowe.Semantics                    as Marlowe
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Effects.WatchAddress (addressChangeRequest)
import           Language.Plutus.Contract.StateMachine         (AsSMContractError (..), StateMachine (..),
                                                                StateMachineClient (..), Void, validatorInstance)
import qualified Language.Plutus.Contract.StateMachine         as SM
import qualified Language.Plutus.Contract.StateMachine.OnChain as SM
import qualified Language.PlutusTx                             as PlutusTx
import qualified Language.PlutusTx.AssocMap                    as AssocMap
import qualified Language.PlutusTx.Prelude                     as P
import           Ledger                                        (CurrencySymbol, Datum (..), Slot (..), SlotRange,
                                                                TokenName, ValidatorCtx (..), mkValidatorScript,
                                                                pubKeyHash, validatorHash, valueSpent)
import qualified Ledger                                        as Ledger
import           Ledger.Ada                                    (adaSymbol, adaValueOf)
import           Ledger.Constraints
import           Ledger.Interval
import           Ledger.Scripts                                (Validator)
import           Ledger.Tx                                     as Tx
import qualified Ledger.Typed.Scripts                          as Scripts
import           Ledger.Typed.Tx                               (TypedScriptTxOut (..), tyTxOutData)
import qualified Ledger.Value                                  as Val
import           Wallet.Types                                  (AddressChangeRequest (..), AddressChangeResponse (..))

type MarloweInput = (SlotRange, [Input])

type MarloweSchema =
    BlockchainActions
        .\/ Endpoint "create" (MarloweParams, Marlowe.Contract)
        .\/ Endpoint "apply-inputs" (MarloweParams, [Input])
        .\/ Endpoint "wait" MarloweParams
        .\/ Endpoint "auto" (MarloweParams, Party)

data MarloweError =
    StateMachineError (SM.SMContractError MarloweData MarloweInput)
    | MarloweEvaluationError TransactionError
    | OtherContractError ContractError
  deriving (Show)

makeClassyPrisms ''MarloweError

instance AsSMContractError MarloweError MarloweData MarloweInput where
    _SMContractError = _StateMachineError

instance AsContractError MarloweError where
    _ContractError = _OtherContractError

instance AsCheckpointError MarloweError where
    _CheckpointError = _OtherContractError . _CheckpointError

data PartyAction
             = PayDeposit AccountId Party Token Integer
             | WaitForTimeout Slot
             | WaitOtherActionUntil Slot
             | NotSure
             | CloseContract
  deriving (Show)

marlowePlutusContract :: forall e. (AsContractError e
    , AsMarloweError e
    , AsCheckpointError e
    , AsSMContractError e MarloweData MarloweInput
    )
    => Contract MarloweSchema e ()
marlowePlutusContract = do
    create `select` wait `select` auto
  where
    create = do
        (params, cont) <- endpoint @"create" @(MarloweParams, Marlowe.Contract) @MarloweSchema
        createContract params cont
        apply `select` wait `select` auto
    wait = do
        params <- endpoint @"wait" @MarloweParams @MarloweSchema
        r <- SM.waitForUpdate (mkMarloweClient params)
        case r of
            Just (TypedScriptTxOut{tyTxOutData=_currentState}, _txOutRef) -> do
                apply `select` wait `select` auto
            Nothing -> pure () -- the contract is closed, no UTxO
    apply = do
        (params, inputs) <- endpoint @"apply-inputs" @(MarloweParams, [Input]) @MarloweSchema
        MarloweData{..}  <- applyInputs params inputs
        case marloweContract of
            Close -> pure ()
            _     -> apply `select` wait `select` auto
    auto = do
        (params, party) <- endpoint @"auto" @(MarloweParams, Party) @MarloweSchema
        let theClient@StateMachineClient{scInstance, scChooser} = mkMarloweClient params
        slot <- currentSlot
        utxo <- utxoAt (SM.machineAddress scInstance)
        let states = SM.getStates scInstance utxo
        case states of
            [] -> do
                wr <- waitForUpdateWithTimeout theClient (slot + 1000)
                case wr of
                    ContractEnded -> do
                        logInfo @String $ "Contract Ended for party" <> show party
                        marlowePlutusContract
                    Timeout _ -> do
                        logInfo @String $ "Contract Timeout for party" <> show party
                        marlowePlutusContract
                    MD md@MarloweData{marloweContract}
                        | canAutoExecuteContractForParty party marloweContract -> autoExecuteContract theClient party md
                    _ -> apply `select` wait `select` auto
            states -> case scChooser states of
                Left err -> do
                    logError @String $ "Chooser err " <> show err
                    apply `select` wait `select` auto
                Right (st, _) -> do
                    let md = tyTxOutData st
                    autoExecuteContract theClient party md


    autoExecuteContract theClient party marloweData = do
        slot <- currentSlot
        let action = getAction slot party marloweData
        case action of
            PayDeposit acc p token amount -> do
                let slotRange = interval slot (slot + 10)
                logInfo @String $ "PayDeposit " <> show amount <> " at slot " <> show slotRange
                let payDeposit = do
                        marloweData <- SM.runStep theClient (slotRange, [IDeposit acc p token amount])
                        continueWith marloweData

                catching (_StateMachineError) payDeposit $ \err -> do
                    logWarn @String $ "Error " <> show err
                    logInfo @String $ "Retry PayDeposit in 2 slots"
                    _ <- awaitSlot (slot + 2)
                    continueWith marloweData
            WaitForTimeout timeout -> do
                logInfo @String $ "WaitForTimeout " <> show timeout
                _ <- awaitSlot timeout
                continueWith marloweData
            WaitOtherActionUntil timeout -> do
                logInfo @String $ "WaitOtherActionUntil " <> show timeout
                wr <- waitForUpdateWithTimeout theClient timeout
                case wr of
                    ContractEnded -> do
                        logInfo @String $ "Contract Ended"
                        pure ()
                    Timeout _ -> do
                        logInfo @String $ "Contract Timeout"
                        continueWith marloweData
                    MD marloweData -> continueWith marloweData

            CloseContract -> do
                logInfo @String $ "CloseContract"
                pure ()

            NotSure -> do
                logInfo @String $ "NotSure"
                apply `select` wait `select` auto

          where
            continueWith = autoExecuteContract theClient party


data WaitingResult
    = Timeout Slot
    | ContractEnded
    | MD MarloweData
  deriving (Show)


waitForUpdateWithTimeout ::
    ( AsSMContractError e MarloweData MarloweInput
    , AsContractError e
    , HasAwaitSlot MarloweSchema
    , HasWatchAddress MarloweSchema)
    => StateMachineClient MarloweData MarloweInput
    -> Timeout
    -> Contract MarloweSchema e WaitingResult
waitForUpdateWithTimeout StateMachineClient{scInstance, scChooser} timeout = do
    let addr = Scripts.scriptAddress $ validatorInstance scInstance
        outputsMap :: Ledger.Tx -> Map.Map TxOutRef TxOutTx
        outputsMap t =
                fmap (\txout -> TxOutTx{txOutTxTx=t, txOutTxOut = txout})
                $ Map.filter ((==) addr . Tx.txOutAddress)
                $ Tx.unspentOutputsTx t
    let go sl = do
            txns <- acrTxns <$> addressChangeRequest AddressChangeRequest{acreqSlot = sl, acreqAddress=addr}
            if null txns && sl < timeout
                then go (succ sl)
                else pure txns

    slot <- currentSlot
    txns <- go slot
    let states = txns >>= SM.getStates scInstance . outputsMap
    case states of
        [] | slot < timeout -> pure ContractEnded
        [] | slot >= timeout -> pure $ Timeout timeout
        xs -> case scChooser xs of
                Left err         -> throwing _SMContractError err
                Right (state, _) -> pure $ MD (tyTxOutData state)


getAction :: Slot -> Party -> MarloweData -> PartyAction
getAction slot party MarloweData{marloweContract,marloweState} = let
    env = Environment (slot, slot + 10)
    in case reduceContractUntilQuiescent env marloweState marloweContract of
        ContractQuiescent _warnings _payments state contract ->
            -- here the contract is either When or Close
            case contract of
                When [Case (Deposit acc depositParty tok value) _] _ _
                    | party == depositParty -> let
                        amount = Marlowe.evalValue env state value
                        in PayDeposit acc party tok amount
                When [Case (Deposit _ depositParty _ _) _] timeout _
                    | party /= depositParty    ->
                        WaitOtherActionUntil timeout
                When [] timeout _ -> WaitForTimeout timeout
                Close -> CloseContract
                _ -> NotSure
        -- When's timeout is in the slot range
        RRAmbiguousSlotIntervalError ->
            {- FIXME
                Consider contract:
                    When [cases] (Slot 100) (When [Case Deposit Close]] (Slot 105) Close)

                For a slot range (95, 105) we get RRAmbiguousSlotIntervalError
                because timeout 100 is inside the slot range.
                Now, we wait for slot 105, and we miss the Deposit.

                To avoid that we need to know what was the original timeout
                that caused RRAmbiguousSlotIntervalError (i.e. Slot 100).
                Then we'd rather wait until slot 100 instead and would make the Deposit.
                I propose to modify RRAmbiguousSlotIntervalError to include the expected timeout.
             -}
            WaitForTimeout (slot + 10)



canAutoExecuteContractForParty :: Party -> Marlowe.Contract -> Bool
canAutoExecuteContractForParty party = check
  where
    check cont =
        case cont of
            Close                                      -> True
            When [] _ cont                             -> check cont
            When [Case (Deposit{}) cont] _ timeoutCont -> check cont && check timeoutCont
            When cases _ timeoutCont                   -> all checkCase cases && check timeoutCont
            Pay _ _ _ _ cont                           -> check cont
            If _ c1 c2                                 -> check c1 && check c2
            Let _ _ cont                               -> check cont
            Assert _ cont                              -> check cont


    checkCase (Case (Choice (ChoiceId _ p) _) cont) | p /= party = check cont
    checkCase _                                     = False


{-| Create a Marlowe contract.
    Uses wallet public key to generate a unique script address.
 -}
createContract :: (AsContractError e, AsSMContractError e MarloweData MarloweInput)
    => MarloweParams
    -> Marlowe.Contract
    -> Contract MarloweSchema e ()
createContract params contract = do
    slot <- currentSlot
    _creator <- pubKeyHash <$> ownPubKey
    let marloweData = MarloweData {
            marloweContract = contract,
            marloweState = emptyState slot }

    let payValue = adaValueOf 0
    let theClient = mkMarloweClient params

    void $ SM.runInitialise theClient marloweData payValue


applyInputs :: (AsContractError e, AsSMContractError e MarloweData MarloweInput)
    => MarloweParams
    -> [Input]
    -> Contract MarloweSchema e MarloweData
applyInputs params inputs = do
    (Slot slot) <- awaitSlot 1
    let slotRange = interval (Slot $ slot - 1)  (Slot $ slot + 10)
    let theClient = mkMarloweClient params
    dat <- SM.runStep theClient (slotRange, inputs)
    return dat


rolePayoutScript :: Validator
rolePayoutScript = mkValidatorScript ($$(PlutusTx.compile [|| wrapped ||]))
  where
    wrapped = Scripts.wrapValidator rolePayoutValidator


{-# INLINABLE rolePayoutValidator #-}
rolePayoutValidator :: (CurrencySymbol, TokenName) -> () -> ValidatorCtx -> Bool
rolePayoutValidator (currency, role) _ ctx =
    Val.valueOf (valueSpent (valCtxTxInfo ctx)) currency role P.> 0


marloweParams :: CurrencySymbol -> MarloweParams
marloweParams rolesCurrency = MarloweParams
    { rolesCurrency = rolesCurrency
    , rolePayoutValidatorHash = validatorHash rolePayoutScript }


defaultMarloweParams :: MarloweParams
defaultMarloweParams = marloweParams adaSymbol


{-# INLINABLE mkMarloweStateMachineTransition #-}
mkMarloweStateMachineTransition
    :: MarloweParams
    -> SM.State MarloweData
    -> MarloweInput
    -> Maybe (TxConstraints Void Void, SM.State MarloweData)
mkMarloweStateMachineTransition params SM.State{ SM.stateData=MarloweData{..}, SM.stateValue=scriptInValue} (range, inputs) = do
    let interval = case range of
            Interval (LowerBound (Finite l) True) (UpperBound (Finite h) True) -> (l, h)
            _ -> P.traceError "Tx valid slot must have lower bound and upper bounds"

    let positiveBalances = validateBalances marloweState ||
            P.traceError "Invalid contract state. There exists an account with non positive balance"

    {-  We do not check that a transaction contains exact input payments.
        We only require an evidence from a party, e.g. a signature for PubKey party,
        or a spend of a 'party role' token.
        This gives huge flexibility by allowing parties to provide multiple
        inputs (either other contracts or P2PKH).
        Then, we check scriptOutput to be correct.
     -}
    let inputsConstraints = validateInputs params inputs

    -- total balance of all accounts in State
    -- accounts must be positive, and we checked it above
    let inputBalance = totalBalance (accounts marloweState)

    -- ensure that a contract TxOut has what it suppose to have
    let balancesOk = inputBalance == scriptInValue

    let preconditionsOk = P.traceIfFalse "Preconditions are false" $ positiveBalances && balancesOk

    let txInput = TransactionInput {
            txInterval = interval,
            txInputs = inputs }

    let computedResult = computeTransaction txInput marloweState marloweContract
    case computedResult of
        TransactionOutput {txOutPayments, txOutState, txOutContract} -> do

            let marloweData = MarloweData {
                    marloweContract = txOutContract,
                    marloweState = txOutState }

            let (deducedTxOutputs, finalBalance) = case txOutContract of
                    Close -> (txPaymentOuts txOutPayments, P.zero)
                    _ -> let
                        txWithPayouts = txPaymentOuts txOutPayments
                        totalPayouts = foldMap (\(Payment _ v) -> v) txOutPayments
                        finalBalance = totalIncome P.- totalPayouts
                        in (txWithPayouts, finalBalance)
            let constraints = inputsConstraints <> deducedTxOutputs <> mustValidateIn range
            if preconditionsOk
            then Just (constraints, SM.State marloweData finalBalance)
            else Nothing
        Error _ -> Nothing

  where
    validateInputWitness :: CurrencySymbol -> Input -> TxConstraints Void Void
    validateInputWitness rolesCurrency input =
        case input of
            IDeposit _ party _ _         -> validatePartyWitness party
            IChoice (ChoiceId _ party) _ -> validatePartyWitness party
            INotify                      -> mempty
      where
        validatePartyWitness (PK pk)     = mustBeSignedBy pk
        validatePartyWitness (Role role) = mustSpendValue (Val.singleton rolesCurrency role 1)

    validateInputs :: MarloweParams -> [Input] -> TxConstraints Void Void
    validateInputs MarloweParams{..} = foldMap (validateInputWitness rolesCurrency)

    collectDeposits :: Input -> Val.Value
    collectDeposits (IDeposit _ _ (Token cur tok) amount) = Val.singleton cur tok amount
    collectDeposits _                                     = P.zero

    totalIncome :: Val.Value
    totalIncome = foldMap collectDeposits inputs

    txPaymentOuts :: [Payment] -> TxConstraints i0 o0
    txPaymentOuts payments = foldMap paymentToTxOut paymentsByParty
      where
        paymentsByParty = AssocMap.toList $ foldr collectPayments AssocMap.empty payments

        paymentToTxOut (party, value) = case party of
            PK pk  -> mustPayToPubKey pk value
            Role role -> let
                dataValue = Datum $ PlutusTx.toData (rolesCurrency params, role)
                in mustPayToOtherScript (rolePayoutValidatorHash params) dataValue value

    collectPayments :: Payment -> AssocMap.Map Party Money -> AssocMap.Map Party Money
    collectPayments (Payment party money) payments = let
        newValue = money P.+ P.fromMaybe P.zero (AssocMap.lookup party payments)
        in AssocMap.insert party newValue payments


{-# INLINABLE isFinal #-}
isFinal :: MarloweData -> Bool
isFinal MarloweData{marloweContract=c} = c P.== Close


{-# INLINABLE mkValidator #-}
mkValidator :: MarloweParams -> Scripts.ValidatorType MarloweStateMachine
mkValidator p = SM.mkValidator $ SM.mkStateMachine (mkMarloweStateMachineTransition p) isFinal


mkMarloweValidatorCode
    :: MarloweParams
    -> PlutusTx.CompiledCode (Scripts.ValidatorType MarloweStateMachine)
mkMarloweValidatorCode params =
    $$(PlutusTx.compile [|| mkValidator ||]) `PlutusTx.applyCode` PlutusTx.liftCode params


type MarloweStateMachine = StateMachine MarloweData MarloweInput

scriptInstance :: MarloweParams -> Scripts.ScriptInstance MarloweStateMachine
scriptInstance params = Scripts.validator @MarloweStateMachine
    (mkMarloweValidatorCode params)
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @MarloweData @MarloweInput


mkMachineInstance :: MarloweParams -> SM.StateMachineInstance MarloweData MarloweInput
mkMachineInstance params =
    SM.StateMachineInstance
    (SM.mkStateMachine (mkMarloweStateMachineTransition params) isFinal)
    (scriptInstance params)


mkMarloweClient :: MarloweParams -> SM.StateMachineClient MarloweData MarloweInput
mkMarloweClient params = SM.mkStateMachineClient (mkMachineInstance params)
