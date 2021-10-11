{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}

module Language.Marlowe.Client where
import           Control.Lens
import           Control.Monad                (forM_, void)
import           Control.Monad.Error.Lens     (catching, throwing)
import           Data.Aeson                   (FromJSON, ToJSON, parseJSON, toJSON)
import qualified Data.List.NonEmpty           as NonEmpty
import           Data.Map.Strict              (Map)
import qualified Data.Map.Strict              as Map
import           Data.Maybe                   (isNothing, maybeToList)
import           Data.Monoid                  (First (..))
import           Data.Semigroup.Generic       (GenericSemigroupMonoid (..))
import qualified Data.Set                     as Set
import qualified Data.Text                    as T
import           Data.UUID                    (UUID)
import           Data.Void                    (absurd)
import           GHC.Generics                 (Generic)
import           Language.Marlowe.Scripts
import           Language.Marlowe.Semantics   hiding (Contract)
import qualified Language.Marlowe.Semantics   as Marlowe
import           Language.Marlowe.Util        (extractContractRoles)
import           Ledger                       (CurrencySymbol, Datum (..), PubKeyHash, Slot (..), TokenName, TxOut (..),
                                               inScripts, pubKeyHash, txOutValue)
import qualified Ledger
import           Ledger.Ada                   (adaSymbol, adaValueOf)
import           Ledger.Address               (pubKeyHashAddress, scriptHashAddress)
import           Ledger.Constraints
import qualified Ledger.Constraints           as Constraints
import           Ledger.Scripts               (datumHash, unitRedeemer)
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Typed.Tx              (TypedScriptTxOut (..), tyTxOutData)
import qualified Ledger.Value                 as Val
import           Plutus.ChainIndex            (_ValidTx, citxInputs, citxOutputs, citxTxId)
import           Plutus.Contract
import           Plutus.Contract.StateMachine (AsSMContractError (..), StateMachineClient (..), Void,
                                               WaitingResult (..))
import qualified Plutus.Contract.StateMachine as SM
import           Plutus.Contract.Wallet       (getUnspentOutput)
import qualified Plutus.Contracts.Currency    as Currency
import qualified PlutusTx
import qualified PlutusTx.AssocMap            as AssocMap

type MarloweSchema =
        Endpoint "create" (UUID, AssocMap.Map Val.TokenName PubKeyHash, Marlowe.Contract)
        .\/ Endpoint "apply-inputs" (UUID, MarloweParams, Maybe SlotInterval, [Input])
        .\/ Endpoint "auto" (UUID, MarloweParams, Party, Slot)
        .\/ Endpoint "redeem" (UUID, MarloweParams, TokenName, PubKeyHash)
        .\/ Endpoint "close" UUID


type MarloweCompanionSchema = EmptySchema
type MarloweFollowSchema = Endpoint "follow" MarloweParams


data MarloweError =
    StateMachineError SM.SMContractError
    | TransitionError (SM.InvalidTransition MarloweData MarloweInput)
    | MarloweEvaluationError TransactionError
    | OtherContractError ContractError
  deriving stock (Eq, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)


makeClassyPrisms ''MarloweError

instance AsSMContractError MarloweError where
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

type RoleOwners = AssocMap.Map Val.TokenName PubKeyHash

data ContractHistory =
    ContractHistory
        { chParams  :: First (MarloweParams, MarloweData)
        , chHistory :: [TransactionInput]
        }
        deriving stock (Show, Generic)
        deriving anyclass (FromJSON, ToJSON)
        deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ContractHistory)

created :: MarloweParams -> MarloweData -> ContractHistory
created p d = mempty{chParams = First (Just (p, d)) }

transition :: TransactionInput -> ContractHistory
transition i = mempty{chHistory = [i] }

isEmpty :: ContractHistory -> Bool
isEmpty = isNothing . getFirst . chParams

data ContractProgress = InProgress | Finished
  deriving stock (Show, Eq, Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Semigroup ContractProgress where
    _ <> Finished     = Finished
    any <> InProgress = any

instance Monoid ContractProgress where
    mempty = InProgress

type EndpointName = String

data LastResult = OK UUID EndpointName | SomeError UUID EndpointName MarloweError | Unknown
  deriving (Show,Eq,Generic)
  deriving anyclass (ToJSON, FromJSON)

instance Semigroup LastResult where
    any <> Unknown = any
    _ <> last      = last

instance Monoid LastResult where
    mempty = Unknown

type MarloweContractState = LastResult


marloweFollowContract :: Contract ContractHistory MarloweFollowSchema MarloweError ()
marloweFollowContract = awaitPromise $ endpoint @"follow" $ \params -> do
    let client = mkMarloweClient params
    let go [] = pure InProgress
        go (tx:rest) = do
            res <- updateHistoryFromTx client params tx
            case res of
                Finished   -> pure Finished
                InProgress -> go rest

    go [] >>= checkpointLoop (follow client params)

  where
    follow client params = \case
        Finished -> do
            logDebug @String ("Contract finished " <> show params)
            pure (Right InProgress) -- do not close the contract so we can see it in Marlowe Run history
        InProgress -> do
            result <- SM.waitForUpdateTimeout @_ @MarloweInput client never >>= awaitPromise
            case result of
                Timeout t -> absurd t
                ContractEnded _ (itvl, inputs) -> do
                    tell @ContractHistory (transition $ TransactionInput itvl inputs)
                    pure (Right Finished)
                Transition _ (itvl, inputs) _ -> do
                    tell @ContractHistory (transition $ TransactionInput itvl inputs)
                    pure (Right InProgress)
                InitialState _ SM.OnChainState{ocsTxOut} -> do
                    let initialMarloweData = tyTxOutData ocsTxOut
                    tell @ContractHistory (created params initialMarloweData)
                    pure (Right InProgress)

    updateHistoryFromTx StateMachineClient{scInstance, scChooser} params tx = do
        logInfo @String $ "Updating history from tx " <> show (view citxTxId tx)
        let inst = SM.typedValidator scInstance
        let address = Scripts.validatorAddress inst
        utxos <- fmap ( Map.filter ((==) address . view Ledger.ciTxOutAddress . fst)
                      . Map.fromList
                      ) $ utxosTxOutTxFromTx tx
        let states = SM.getStates scInstance utxos
        case findInput inst tx of
            -- if there's no TxIn for Marlowe contract that means
            -- it's a contract creation transaction, and there is Marlowe TxOut
            Nothing -> case scChooser states of
                Left err    -> throwing _SMContractError err
                Right SM.OnChainState{SM.ocsTxOut=state} -> do
                    let initialMarloweData = tyTxOutData state
                    logInfo @String ("Contract created " <> show initialMarloweData)
                    tell $ created params initialMarloweData
                    pure InProgress
            -- There is TxIn with Marlowe contract, hence this is a state transition
            Just (interval, inputs) -> do
                let txInput = TransactionInput {
                        txInterval = interval,
                        txInputs = inputs }
                tell $ transition txInput
                case states of
                    -- when there is no Marlowe TxOut the contract is closed
                    -- and we can close the follower contract
                    [] -> pure Finished
                    -- otherwise we continue following
                    _  -> pure InProgress

    findInput inst tx = do
        let inputs = Set.toList (view citxInputs tx) >>= maybeToList . inScripts
        let script = Scripts.validatorScript inst
        -- find previous Marlowe contract
        let marloweTxInputs = filter (\(validator, _, _) -> validator == script) inputs
        case marloweTxInputs of
            []                          -> Nothing
            [(_, Ledger.Redeemer d, _)] -> PlutusTx.fromBuiltinData d
            _                           -> Nothing

{-  This is a control contract.
    It allows to create a contract, apply inputs, auto-execute a contract,
    redeem role payouts, and close.
 -}
marlowePlutusContract :: Contract MarloweContractState MarloweSchema MarloweError ()
marlowePlutusContract = selectList [create, apply, auto, redeem, close]
  where
    catchError reqId endpointName handler = catching _MarloweError
        (void $ mapError (review _MarloweError) handler)
        (\er -> do
            tell $ SomeError reqId endpointName er
            marlowePlutusContract)
    create = endpoint @"create" $ \(reqId, owners, contract) -> catchError reqId "create" $ do
        -- Create a transaction with the role tokens and pay them to the contract creator
        -- See Note [The contract is not ready]
        (params, distributeRoleTokens, lkps) <- setupMarloweParams owners contract
        slot <- currentSlot
        let StateMachineClient{scInstance} = mkMarloweClient params
        let marloweData = MarloweData {
                marloweContract = contract,
                marloweState = emptyState slot }
        let payValue = adaValueOf 0
        let SM.StateMachineInstance{SM.typedValidator} = scInstance
        let tx = mustPayToTheScript marloweData payValue <> distributeRoleTokens
        let lookups = Constraints.typedValidatorLookups typedValidator <> lkps
        -- Create the Marlowe contract and pay the role tokens to the owners
        utx <- either (throwing _ConstraintResolutionError) pure (Constraints.mkTx lookups tx)
        submitTxConfirmed utx
        tell $ OK reqId "create"
        marlowePlutusContract
    apply = endpoint @"apply-inputs" $ \(reqId, params, slotInterval, inputs) -> catchError reqId "apply-inputs" $ do
        _ <- applyInputs params slotInterval inputs
        tell $ OK reqId "apply-inputs"
        marlowePlutusContract
    redeem = promiseMap (mapError (review _MarloweError)) $ endpoint @"redeem" $ \(reqId, MarloweParams{rolesCurrency}, role, pkh) -> catchError reqId "redeem" $ do
        let address = scriptHashAddress (mkRolePayoutValidatorHash rolesCurrency)
        utxos <- utxosAt address
        let spendPayoutConstraints tx ref txout = let
                expectedDatumHash = datumHash (Datum $ PlutusTx.toBuiltinData role)
                amount = view Ledger.ciTxOutValue txout
                dh = either id Ledger.datumHash <$> preview Ledger.ciTxOutDatum txout
                in case dh of
                    Just datumHash | datumHash == expectedDatumHash ->
                        -- we spend the rolePayoutScript address
                        Constraints.mustSpendScriptOutput ref unitRedeemer
                        -- and pay to a token owner
                            <> Constraints.mustPayToPubKey pkh amount
                    _ -> tx

        let spendPayouts = Map.foldlWithKey spendPayoutConstraints mempty utxos
        if spendPayouts == mempty
        then do
            tell $ OK reqId "redeem"
        else do
            let
              constraints = spendPayouts
                  -- must spend a role token for authorization
                  <> Constraints.mustSpendAtLeast (Val.singleton rolesCurrency role 1)
              -- lookup for payout validator and role payouts
              validator = rolePayoutScript rolesCurrency
              lookups = Constraints.otherScript validator
                  <> Constraints.unspentOutputs utxos
                  <> Constraints.ownPubKeyHash pkh
            tx <- either (throwing _ConstraintResolutionError) pure (Constraints.mkTx @Void lookups constraints)
            _ <- submitUnbalancedTx tx
            tell $ OK reqId "redeem"

        marlowePlutusContract
    auto = endpoint @"auto" $ \(reqId, params, party, untilSlot) -> catchError reqId "auto" $ do
        let theClient = mkMarloweClient params
        let continueWith :: MarloweData -> Contract MarloweContractState MarloweSchema MarloweError ()
            continueWith md@MarloweData{marloweContract} =
                if canAutoExecuteContractForParty party marloweContract
                then autoExecuteContract reqId theClient party md
                else do
                    tell $ OK reqId "auto"
                    marlowePlutusContract

        maybeState <- SM.getOnChainState theClient
        case maybeState of
            Nothing -> do
                wr <- SM.waitForUpdateUntilSlot theClient untilSlot
                case wr of
                    ContractEnded{} -> do
                        logInfo @String $ "Contract Ended for party " <> show party
                        tell $ OK reqId "auto"
                        marlowePlutusContract
                    Timeout{} -> do
                        logInfo @String $ "Contract Timeout for party " <> show party
                        tell $ OK reqId "auto"
                        marlowePlutusContract
                    Transition _ _ marloweData -> continueWith marloweData
                    InitialState _ marloweData -> continueWith marloweData
            Just (SM.OnChainState{SM.ocsTxOut=st}, _) -> do
                let marloweData = tyTxOutData st
                continueWith marloweData
    -- The MarloweApp contract is closed implicitly by not returning
    -- itself (marlowePlutusContract) as a continuation
    close = endpoint @"close" $ \reqId -> tell $ OK reqId "close"


    autoExecuteContract :: UUID
                      -> StateMachineClient MarloweData MarloweInput
                      -> Party
                      -> MarloweData
                      -> Contract MarloweContractState MarloweSchema MarloweError ()
    autoExecuteContract reqId theClient party marloweData = do
        slot <- currentSlot
        let slotRange = (slot, slot + defaultTxValidationRange)
        let action = getAction slotRange party marloweData
        case action of
            PayDeposit acc p token amount -> do
                logInfo @String $ "PayDeposit " <> show amount <> " at within slots " <> show slotRange
                let payDeposit = do
                        marloweData <- SM.runStep theClient (slotRange, [IDeposit acc p token amount])
                        case marloweData of
                            SM.TransitionFailure e -> throwing _TransitionError e
                            SM.TransitionSuccess d -> continueWith d

                catching _StateMachineError payDeposit $ \err -> do
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
                wr <- SM.waitForUpdateUntilSlot theClient timeout
                case wr of
                    ContractEnded{} -> do
                        logInfo @String $ "Contract Ended"
                        tell $ OK reqId "auto"
                        marlowePlutusContract
                    Timeout{} -> do
                        logInfo @String $ "Contract Timeout"
                        continueWith marloweData
                    Transition _ _ marloweData -> continueWith marloweData
                    InitialState _ marloweData -> continueWith marloweData

            CloseContract -> do
                logInfo @String $ "CloseContract"
                tell $ OK reqId "auto"
                marlowePlutusContract

            NotSure -> do
                logInfo @String $ "NotSure"
                tell $ OK reqId "auto"
                marlowePlutusContract

          where
            continueWith = autoExecuteContract reqId theClient party


setupMarloweParams
    :: forall s e i o.
    (AsMarloweError e)
    => RoleOwners
    -> Marlowe.Contract
    -> Contract MarloweContractState s e
        (MarloweParams, TxConstraints i o, ScriptLookups (SM.StateMachine MarloweData MarloweInput))
setupMarloweParams owners contract = mapError (review _MarloweError) $ do
    creator <- pubKeyHash <$> ownPubKey
    let ownAddress = pubKeyHashAddress creator
    let roles = extractContractRoles contract
    if Set.null roles
    then do
        let params = MarloweParams
                { rolesCurrency = adaSymbol
                , rolePayoutValidatorHash = defaultRolePayoutValidatorHash }
        pure (params, mempty, mempty)
    else if roles `Set.isSubsetOf` Set.fromList (AssocMap.keys owners)
    then do
        let tokens = fmap (\role -> (role, 1)) $ Set.toList roles
        txOutRef@(Ledger.TxOutRef h i) <- getUnspentOutput
        utxo <- utxosAt ownAddress
        let theCurrency = Currency.OneShotCurrency
                { curRefTransactionOutput = (h, i)
                , curAmounts              = AssocMap.fromList tokens
                }
            curVali     = Currency.curPolicy theCurrency
            lookups     = Constraints.mintingPolicy curVali
                            <> Constraints.unspentOutputs utxo
            mintTx      = Constraints.mustSpendPubKeyOutput txOutRef
                            <> Constraints.mustMintValue (Currency.mintedValue theCurrency)
        let rolesSymbol = Ledger.scriptCurrencySymbol curVali
        let giveToParty (role, pkh) = Constraints.mustPayToPubKey pkh (Val.singleton rolesSymbol role 1)
        let distributeRoleTokens = foldMap giveToParty (AssocMap.toList owners)
        let params = MarloweParams
                { rolesCurrency = rolesSymbol
                , rolePayoutValidatorHash = mkRolePayoutValidatorHash rolesSymbol }
        pure (params, mintTx <> distributeRoleTokens, lookups)
    else do
        let missingRoles = roles `Set.difference` Set.fromList (AssocMap.keys owners)
        let message = T.pack $ "You didn't specify owners of these roles: " <> show missingRoles
        throwing _ContractError $ OtherError message


getAction :: MarloweSlotRange -> Party -> MarloweData -> PartyAction
getAction slotRange party MarloweData{marloweContract,marloweState} = let
    env = Environment slotRange
    in case reduceContractUntilQuiescent env marloweState marloweContract of
        ContractQuiescent _reduced _warnings _payments state contract ->
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
        -- When timeout is in the slot range
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
            Close                                    -> True
            When [] _ cont                           -> check cont
            When [Case Deposit{} cont] _ timeoutCont -> check cont && check timeoutCont
            When cases _ timeoutCont                 -> all checkCase cases && check timeoutCont
            Pay _ _ _ _ cont                         -> check cont
            If _ c1 c2                               -> check c1 && check c2
            Let _ _ cont                             -> check cont
            Assert _ cont                            -> check cont


    checkCase (Case (Choice (ChoiceId _ p) _) cont) | p /= party = check cont
    checkCase _                                     = False


applyInputs :: AsMarloweError e
    => MarloweParams
    -> Maybe SlotInterval
    -> [Input]
    -> Contract MarloweContractState MarloweSchema e MarloweData
applyInputs params slotInterval inputs = mapError (review _MarloweError) $ do
    slotRange <- case slotInterval of
            Just si -> pure si
            Nothing -> do
                slot <- currentSlot
                pure (slot, slot + defaultTxValidationRange)
    let theClient = mkMarloweClient params
    dat <- SM.runStep theClient (slotRange, inputs)
    case dat of
        SM.TransitionFailure e -> do
            logError e
            throwing _TransitionError e
        SM.TransitionSuccess d -> return d

marloweParams :: CurrencySymbol -> MarloweParams
marloweParams rolesCurrency = MarloweParams
    { rolesCurrency = rolesCurrency
    , rolePayoutValidatorHash = mkRolePayoutValidatorHash rolesCurrency }


defaultMarloweParams :: MarloweParams
defaultMarloweParams = marloweParams adaSymbol


newtype CompanionState = CompanionState (Map MarloweParams MarloweData)
  deriving (Semigroup,Monoid) via (Map MarloweParams MarloweData)

instance ToJSON CompanionState where
    toJSON (CompanionState m) = toJSON $ Map.toList m

instance FromJSON CompanionState where
    parseJSON v = CompanionState . Map.fromList <$> parseJSON v

{-|
    Contract that monitors a user wallet for receiving a Marlowe role token.
    When it sees that a Marlowe contract exists on chain with a role currency
    of a token the user owns it updates its @CompanionState@
    with contract's @MarloweParams@ and @MarloweData@
-}
marloweCompanionContract :: Contract CompanionState MarloweCompanionSchema MarloweError ()
marloweCompanionContract = checkExistingRoleTokens
  where
    checkExistingRoleTokens = do
        -- Get the existing unspend outputs of the wallet that activated the companion contract
        pkh <- pubKeyHash <$> ownPubKey
        let ownAddress = pubKeyHashAddress pkh
        -- Filter those outputs for role tokens and notify the WebSocket subscribers
        -- NOTE: CombinedWSStreamToServer has an API to subscribe to WS notifications
        utxo <- utxosAt ownAddress
        let txOuts = fmap Ledger.toTxOut $ Map.elems utxo
        forM_ txOuts notifyOnNewContractRoles
        -- This contract will run in a loop forever (because we always return Right)
        -- checking for updates to the UTXO's for a given address.
        -- The contract could be stopped via /contract/<instance>/stop but we are
        -- currently not doing that.
        checkpointLoop (fmap Right <$> checkForUpdates) ownAddress
    checkForUpdates ownAddress = do
        txns <- NonEmpty.toList <$> awaitUtxoProduced ownAddress
        let txOuts = txns >>= view (citxOutputs . _ValidTx)
        forM_ txOuts notifyOnNewContractRoles
        pure ownAddress

notifyOnNewContractRoles :: TxOut
    -> Contract CompanionState MarloweCompanionSchema MarloweError ()
notifyOnNewContractRoles txout = do
    -- Filter the CurrencySymbol's of this transaction output that might be
    -- a role token symbol. Basically, any non-ADA symbols is a prospect to
    -- to be a role token, but it could also be an NFT for example.
    let curSymbols = filterRoles txout
    forM_ curSymbols $ \cs -> do
        -- Check if there is a Marlowe contract on chain that uses this currency
        contract <- findMarloweContractsOnChainByRoleCurrency cs
        case contract of
            Just (params, md) -> do
                logDebug @String $ "Companion contract: Updating observable state"
                tell $ CompanionState (Map.singleton params md)
            Nothing           -> do
            -- The result will be empty if:
            --   * Note [The contract is not ready]: When you create a Marlowe contract first we create
            --                                       the role tokens, pay them to the contract creator and
            --                                       then we create the Marlowe contract.
            --   * If the marlowe contract is closed.
                -- TODO: Change for debug
                logWarn @String $ "Companion contract: On-chain state not found!"
                pure ()


filterRoles :: TxOut -> [CurrencySymbol]
filterRoles TxOut { txOutValue, txOutDatumHash = Nothing } =
    let curSymbols = filter (/= adaSymbol) $ AssocMap.keys $ Val.getValue txOutValue
    in  curSymbols
filterRoles _ = []


findMarloweContractsOnChainByRoleCurrency
    :: CurrencySymbol
    -> Contract CompanionState
                MarloweCompanionSchema
                MarloweError
                (Maybe (MarloweParams, MarloweData))
findMarloweContractsOnChainByRoleCurrency curSym = do
    let params = marloweParams curSym
    let client = mkMarloweClient params
    maybeState <- SM.getOnChainState client
    case maybeState of
        Just (SM.OnChainState{SM.ocsTxOut}, _) -> do
            let marloweData = tyTxOutData ocsTxOut
            pure $ Just (params, marloweData)
        Nothing -> pure Nothing
