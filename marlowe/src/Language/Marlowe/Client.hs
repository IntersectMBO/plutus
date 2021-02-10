{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
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
import           Control.Monad.Error.Lens                          (catching, throwing)
import           Data.Aeson                                        (FromJSON, ToJSON)
import qualified Data.Map.Strict                                   as Map
import qualified Data.Set                                          as Set
import qualified Data.Text                                         as T
import           GHC.Generics                                      (Generic)
import           Language.Marlowe.Semantics                        hiding (Contract)
import qualified Language.Marlowe.Semantics                        as Marlowe
import           Language.Marlowe.Util                             (extractContractRoles)
import           Language.Plutus.Contract
import           Language.Plutus.Contract.StateMachine             (AsSMContractError (..), StateMachine (..),
                                                                    StateMachineClient (..), StateMachineInstance (..),
                                                                    Void, WaitingResult (..))
import qualified Language.Plutus.Contract.StateMachine             as SM
import qualified Language.PlutusTx                                 as PlutusTx
import qualified Language.PlutusTx.AssocMap                        as AssocMap
import qualified Language.PlutusTx.Coordination.Contracts.Currency as Currency
import qualified Language.PlutusTx.Prelude                         as P
import           Ledger                                            (Address (..), CurrencySymbol, Datum (..),
                                                                    PubKeyHash, Slot (..), TokenName, TxOutTx (..),
                                                                    ValidatorCtx (..), ValidatorHash, mkValidatorScript,
                                                                    pubKeyHash, txOutDatum, txOutValue, validatorHash,
                                                                    valueSpent)
import           Ledger.Ada                                        (adaSymbol, adaValueOf)
import           Ledger.Constraints
import qualified Ledger.Constraints                                as Constraints
import qualified Ledger.Interval                                   as Interval
import           Ledger.Scripts                                    (Validator, datumHash, unitRedeemer)
import qualified Ledger.Typed.Scripts                              as Scripts
import           Ledger.Typed.Tx                                   (TypedScriptTxOut (..), tyTxOutData)
import qualified Ledger.Value                                      as Val

type MarloweSlotRange = (Slot, Slot)
type MarloweInput = (MarloweSlotRange, [Input])

type MarloweSchema =
    BlockchainActions
        .\/ Endpoint "create" (AssocMap.Map Val.TokenName PubKeyHash, Marlowe.Contract)
        .\/ Endpoint "apply-inputs" (MarloweParams, [Input])
        .\/ Endpoint "wait" MarloweParams
        .\/ Endpoint "auto" (MarloweParams, Party, Slot)
        .\/ Endpoint "redeem" (MarloweParams, TokenName, PubKeyHash)

data MarloweError =
    StateMachineError SM.SMContractError
    | TransitionError (SM.InvalidTransition MarloweData MarloweInput)
    | MarloweEvaluationError TransactionError
    | OtherContractError ContractError
    | RolesCurrencyError Currency.CurrencyError
  deriving stock (Show, Generic)
  deriving anyclass (ToJSON, FromJSON)


makeClassyPrisms ''MarloweError

instance AsSMContractError MarloweError where
    _SMContractError = _StateMachineError

instance AsContractError MarloweError where
    _ContractError = _OtherContractError

instance AsCheckpointError MarloweError where
    _CheckpointError = _OtherContractError . _CheckpointError

instance Currency.AsCurrencyError MarloweError where
    _CurrencyError = _RolesCurrencyError

data PartyAction
             = PayDeposit AccountId Party Token Integer
             | WaitForTimeout Slot
             | WaitOtherActionUntil Slot
             | NotSure
             | CloseContract
  deriving (Show)

type RoleOwners = AssocMap.Map Val.TokenName PubKeyHash

marlowePlutusContract :: Contract MarloweSchema MarloweError ()
marlowePlutusContract = do
    create `select` apply `select` wait `select` auto `select` redeem
  where
    create = do
        (owners, contract) <- endpoint @"create"
            @(AssocMap.Map Val.TokenName PubKeyHash, Marlowe.Contract)
            @MarloweSchema
        (params, distributeRoleTokens) <- setupMarloweParams owners contract
        slot <- currentSlot
        let StateMachineClient{scInstance} = mkMarloweClient params
        let marloweData = MarloweData {
                marloweContract = contract,
                marloweState = emptyState slot }
        let payValue = adaValueOf 0
        let StateMachineInstance{validatorInstance} = scInstance
        let tx = mustPayToTheScript marloweData payValue <> distributeRoleTokens
        let lookups = Constraints.scriptInstanceLookups validatorInstance
        utx <- either (throwing _ConstraintResolutionError) pure (Constraints.mkTx lookups tx)
        submitTxConfirmed utx
        marlowePlutusContract
    wait = do
        params <- endpoint @"wait" @MarloweParams @MarloweSchema
        _ <- SM.waitForUpdate (mkMarloweClient params)
        marlowePlutusContract
    apply = do
        (params, inputs) <- endpoint @"apply-inputs" @(MarloweParams, [Input]) @MarloweSchema
        _ <- applyInputs params inputs
        marlowePlutusContract
    redeem = mapError (review _MarloweError) $ do
        (MarloweParams{rolesCurrency}, role, pkh) <-
            endpoint @"redeem" @(MarloweParams, TokenName, PubKeyHash) @MarloweSchema
        let address = ScriptAddress (mkRolePayoutValidatorHash rolesCurrency)
        utxos <- utxoAt address
        let spendPayoutConstraints tx ref TxOutTx{txOutTxOut} = let
                expectedDatumHash = datumHash (Datum $ PlutusTx.toData role)
                amount = txOutValue txOutTxOut
                in case txOutDatum txOutTxOut of
                    Just datumHash | datumHash == expectedDatumHash ->
                        -- we spend the rolePayoutScript address
                        Constraints.mustSpendScriptOutput ref unitRedeemer
                        -- and pay to a token owner
                            <> Constraints.mustPayToPubKey pkh amount
                    _ -> tx

        let spendPayouts = Map.foldlWithKey spendPayoutConstraints mempty utxos
            constraints = spendPayouts
                -- must spend a role token for authorization
                <> Constraints.mustSpendValue (Val.singleton rolesCurrency role 1)
            -- lookup for payout validator and role payouts
            validator = rolePayoutScript rolesCurrency
            lookups = Constraints.otherScript validator
                <> Constraints.unspentOutputs utxos
                <> Constraints.ownPubKeyHash pkh
        tx <- either (throwing _ConstraintResolutionError) pure (Constraints.mkTx @Void lookups constraints)
        _ <- submitUnbalancedTx tx
        marlowePlutusContract
    auto = do
        (params, party, untilSlot) <- endpoint @"auto" @(MarloweParams, Party, Slot) @MarloweSchema
        let theClient = mkMarloweClient params
        let continueWith :: MarloweData -> Contract MarloweSchema MarloweError ()
            continueWith md@MarloweData{marloweContract} =
                if canAutoExecuteContractForParty party marloweContract
                then autoExecuteContract theClient party md
                else marlowePlutusContract

        maybeState <- SM.getOnChainState theClient
        case maybeState of
            Nothing -> do
                wr <- SM.waitForUpdateUntil theClient untilSlot
                case wr of
                    ContractEnded -> do
                        logInfo @String $ "Contract Ended for party " <> show party
                        marlowePlutusContract
                    Timeout _ -> do
                        logInfo @String $ "Contract Timeout for party " <> show party
                        marlowePlutusContract
                    WaitingResult marloweData -> continueWith marloweData
            Just ((st, _), _) -> do
                let marloweData = tyTxOutData st
                continueWith marloweData


    autoExecuteContract :: StateMachineClient MarloweData MarloweInput
                      -> Party
                      -> MarloweData
                      -> Contract MarloweSchema MarloweError ()
    autoExecuteContract theClient party marloweData = do
        slot <- currentSlot
        let slotRange = (slot, slot + defaultTxValidationRange)
        let action = getAction slotRange party marloweData
        case action of
            PayDeposit acc p token amount -> do
                logInfo @String $ "PayDeposit " <> show amount <> " at whithin slots " <> show slotRange
                let payDeposit = do
                        marloweData <- SM.runStep theClient (slotRange, [IDeposit acc p token amount])
                        case marloweData of
                            SM.TransitionFailure e -> throwing _TransitionError e
                            SM.TransitionSuccess d -> continueWith d

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
                wr <- SM.waitForUpdateUntil theClient timeout
                case wr of
                    ContractEnded -> do
                        logInfo @String $ "Contract Ended"
                        marlowePlutusContract
                    Timeout _ -> do
                        logInfo @String $ "Contract Timeout"
                        continueWith marloweData
                    WaitingResult marloweData -> continueWith marloweData

            CloseContract -> do
                logInfo @String $ "CloseContract"
                marlowePlutusContract

            NotSure -> do
                logInfo @String $ "NotSure"
                marlowePlutusContract

          where
            continueWith = autoExecuteContract theClient party


setupMarloweParams
    :: forall s e i o.
       ( HasWriteTx s
       , HasOwnPubKey s
       , HasTxConfirmation s
       , AsMarloweError e
       )
    => RoleOwners -> Marlowe.Contract -> Contract s e (MarloweParams, TxConstraints i o)
setupMarloweParams owners contract = mapError (review _MarloweError) $ do
    creator <- pubKeyHash <$> ownPubKey
    let roles = extractContractRoles contract
    if Set.null roles
    then do
        let params = MarloweParams
                { rolesCurrency = adaSymbol
                , rolePayoutValidatorHash = defaultRolePayoutValidatorHash }
        pure (params, mempty)
    else if roles `Set.isSubsetOf` Set.fromList (AssocMap.keys owners)
    then do
        let tokens = fmap (\role -> (role, 1)) $ Set.toList roles
        cur <- mapError RolesCurrencyError $ Currency.forgeContract creator tokens
        let rolesSymbol = Currency.currencySymbol cur
        let giveToParty (role, pkh) = Constraints.mustPayToPubKey pkh (Val.singleton rolesSymbol role 1)
        let distributeRoleTokens = foldMap giveToParty (AssocMap.toList owners)
        let params = MarloweParams
                { rolesCurrency = rolesSymbol
                , rolePayoutValidatorHash = mkRolePayoutValidatorHash rolesSymbol }
        pure (params, distributeRoleTokens)
    else do
        let missingRoles = roles `Set.difference` Set.fromList (AssocMap.keys owners)
        let message = T.pack $ "You didn't specify owners of these roles: " <> show missingRoles
        throwing _ContractError $ OtherError message


getAction :: MarloweSlotRange -> Party -> MarloweData -> PartyAction
getAction slotRange party MarloweData{marloweContract,marloweState} = let
    env = Environment slotRange
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
            WaitForTimeout (snd slotRange)



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


applyInputs :: (AsContractError e, AsSMContractError e, AsMarloweError e)
    => MarloweParams
    -> [Input]
    -> Contract MarloweSchema e MarloweData
applyInputs params inputs = do
    slot <- currentSlot
    let slotRange = (slot, slot + defaultTxValidationRange)
    let theClient = mkMarloweClient params
    dat <- SM.runStep theClient (slotRange, inputs)
    case dat of
        SM.TransitionFailure e -> do
            logError e
            throwing _TransitionError e
        SM.TransitionSuccess d -> return d

rolePayoutScript :: CurrencySymbol -> Validator
rolePayoutScript symbol = mkValidatorScript ($$(PlutusTx.compile [|| wrapped ||]) `PlutusTx.applyCode` PlutusTx.liftCode symbol)
  where
    wrapped s = Scripts.wrapValidator (rolePayoutValidator s)


{-# INLINABLE rolePayoutValidator #-}
rolePayoutValidator :: CurrencySymbol -> TokenName -> () -> ValidatorCtx -> Bool
rolePayoutValidator currency role _ ctx =
    Val.valueOf (valueSpent (valCtxTxInfo ctx)) currency role P.> 0


mkRolePayoutValidatorHash :: CurrencySymbol -> ValidatorHash
mkRolePayoutValidatorHash symbol = validatorHash (rolePayoutScript symbol)


defaultRolePayoutValidatorHash :: ValidatorHash
defaultRolePayoutValidatorHash = mkRolePayoutValidatorHash adaSymbol

marloweParams :: CurrencySymbol -> MarloweParams
marloweParams rolesCurrency = MarloweParams
    { rolesCurrency = rolesCurrency
    , rolePayoutValidatorHash = mkRolePayoutValidatorHash rolesCurrency }


defaultMarloweParams :: MarloweParams
defaultMarloweParams = marloweParams adaSymbol


{-# INLINABLE mkMarloweStateMachineTransition #-}
mkMarloweStateMachineTransition
    :: MarloweParams
    -> SM.State MarloweData
    -> MarloweInput
    -> Maybe (TxConstraints Void Void, SM.State MarloweData)
mkMarloweStateMachineTransition params SM.State{ SM.stateData=MarloweData{..}, SM.stateValue=scriptInValue}
    (interval@(minSlot, maxSlot), inputs) = do
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

            let (outputsConstraints, finalBalance) = case txOutContract of
                    Close -> (payoutContraints txOutPayments, P.zero)
                    _ -> let
                        outputsConstraints = payoutContraints txOutPayments
                        totalIncome = P.foldMap collectDeposits inputs
                        totalPayouts = P.foldMap (\(Payment _ v) -> v) txOutPayments
                        finalBalance = totalIncome P.- totalPayouts
                        in (outputsConstraints, finalBalance)
            let range = Interval.interval minSlot maxSlot
            let constraints = inputsConstraints <> outputsConstraints <> mustValidateIn range
            if preconditionsOk
            then Just (constraints, SM.State marloweData finalBalance)
            else Nothing
        Error _ -> Nothing

  where
    validateInputs :: MarloweParams -> [Input] -> TxConstraints Void Void
    validateInputs MarloweParams{rolesCurrency} inputs = let
        (keys, roles) = P.foldMap validateInputWitness inputs
        mustSpendSetOfRoleTokens = P.foldMap mustSpendRoleToken (AssocMap.keys roles)
        in P.foldMap mustBeSignedBy keys P.<> mustSpendSetOfRoleTokens
      where
        validateInputWitness :: Input -> ([PubKeyHash], AssocMap.Map TokenName ())
        validateInputWitness input =
            case input of
                IDeposit _ party _ _         -> validatePartyWitness party
                IChoice (ChoiceId _ party) _ -> validatePartyWitness party
                INotify                      -> (P.mempty, P.mempty)
          where
            validatePartyWitness (PK pk)     = ([pk], P.mempty)
            validatePartyWitness (Role role) = ([], AssocMap.singleton role ())

        mustSpendRoleToken :: TokenName -> TxConstraints Void Void
        mustSpendRoleToken role = mustSpendValue $ Val.singleton rolesCurrency role 1

    collectDeposits :: Input -> Val.Value
    collectDeposits (IDeposit _ _ (Token cur tok) amount) = Val.singleton cur tok amount
    collectDeposits _                                     = P.zero

    payoutContraints :: [Payment] -> TxConstraints i0 o0
    payoutContraints payments = P.foldMap paymentToTxOut paymentsByParty
      where
        paymentsByParty = AssocMap.toList $ P.foldMap paymentByParty payments

        paymentToTxOut (party, value) = case party of
            PK pk  -> mustPayToPubKey pk value
            Role role -> let
                dataValue = Datum $ PlutusTx.toData role
                in mustPayToOtherScript (rolePayoutValidatorHash params) dataValue value

        paymentByParty (Payment party money) = AssocMap.singleton party money


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


defaultTxValidationRange :: Slot
defaultTxValidationRange = 10
