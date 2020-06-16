{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Playground.Interpreter.Util
    ( stage
    ) where

import           Control.Lens                                    (view)
import           Control.Monad.Except                            (throwError)
import           Data.Aeson                                      (FromJSON, eitherDecode)
import qualified Data.Aeson                                      as JSON
import           Data.Bifunctor                                  (first)
import           Data.ByteString.Lazy                            (ByteString)
import qualified Data.ByteString.Lazy.Char8                      as BSL
import           Data.Foldable                                   (traverse_)
import           Data.Map                                        (Map)
import qualified Data.Map                                        as Map
import           Data.Row                                        (Forall)
import           Data.Row.Internal                               (Unconstrained1)
import           Data.Text                                       (Text)
import qualified Data.Text                                       as Text
import qualified Data.Text.Encoding                              as Text
import           Data.Text.Prettyprint.Doc                       (Pretty)
import           Language.Plutus.Contract                        (Contract, ContractRow, HasAwaitSlot,
                                                                  HasBlockchainActions)
import           Language.Plutus.Contract.Effects.ExposeEndpoint (EndpointDescription, getEndpointDescription)
import           Language.Plutus.Contract.Schema                 (Event, Input, Output)
import           Language.Plutus.Contract.Test                   (renderTraceContext)
import           Language.Plutus.Contract.Trace                  (ContractTrace, ContractTraceState,
                                                                  TraceError (TContractError), addBlocks,
                                                                  addBlocksUntil, addNamedEvent, handleBlockchainEvents,
                                                                  notifyInterestingAddresses, notifySlot, payToWallet,
                                                                  runTraceWithDistribution)
import           Ledger                                          (Blockchain, PubKey, TxOut (txOutValue), pubKeyHash,
                                                                  txOutTxOut)
import           Ledger.AddressMap                               (fundsAt)
import           Ledger.Value                                    (Value)
import qualified Ledger.Value                                    as Value
import           Playground.Types                                (ContractCall (AddBlocks, AddBlocksUntil, CallEndpoint, PayToWallet),
                                                                  EvaluationResult (EvaluationResult), Expression,
                                                                  FunctionSchema (FunctionSchema),
                                                                  PlaygroundError (JsonDecodingError, OtherError, RollupError),
                                                                  SimulatorWallet (SimulatorWallet), amount, argument,
                                                                  argumentValues, blocks, caller, decodingError,
                                                                  emulatorLog, emulatorTrace, endpointDescription,
                                                                  expected, fundsDistribution, input, recipient,
                                                                  resultBlockchain, resultRollup, sender,
                                                                  simulatorWalletBalance, simulatorWalletWallet, slot,
                                                                  walletKeys)
import           Wallet.Emulator                                 (MonadEmulator)
import           Wallet.Emulator.Chain                           (ChainState (ChainState), _chainNewestFirst, _index,
                                                                  _txPool)
import           Wallet.Emulator.NodeClient                      (NodeClientState, clientIndex)
import           Wallet.Emulator.Types                           (EmulatorEvent, EmulatorState (EmulatorState, _chainState, _emulatorLog, _walletClientStates),
                                                                  Wallet)
import           Wallet.Emulator.Wallet                          (walletAddress, walletPubKey)
import           Wallet.Rollup                                   (doAnnotateBlockchain)

-- | Unfortunately any uncaught errors in the interpreter kill the
-- thread that is running it rather than returning the error. This
-- means we need to handle all expected errors in the expression we
-- are interpreting. This gets a little tricky because we have to
-- decode JSON inside the interpreter (since we don't have access to
-- it's type outside) so we need to wrap the @apply functions up in
-- something that can throw errors.
type TraceResult
     = ( Blockchain
       , [EmulatorEvent]
       , Text
       , [SimulatorWallet]
       , [(PubKey, Wallet)])

analyzeEmulatorState ::
       forall s a.
       (Forall (Input s) Pretty, Forall (Output s) Pretty)
    => ContractTraceState s (TraceError Text) a
    -> EmulatorState
    -> Either PlaygroundError EvaluationResult
analyzeEmulatorState traceState EmulatorState { _chainState = ChainState { _chainNewestFirst
                                                                         , _txPool
                                                                         , _index
                                                                         }
                                              , _walletClientStates
                                              , _emulatorLog
                                              } =
    postProcessEvaluation traceResult
  where
    traceResult :: TraceResult
    traceResult =
        ( _chainNewestFirst
        , _emulatorLog
        , _emulatorTrace
        , fundsDistribution
        , Map.foldMapWithKey toKeyWalletPair _walletClientStates)
    _emulatorTrace = renderTraceContext mempty traceState
    fundsDistribution :: [SimulatorWallet]
    fundsDistribution =
        filter (not . Value.isZero . simulatorWalletBalance) $
        Map.foldMapWithKey (\k v -> [toSimulatorWallet k v]) _walletClientStates
    toSimulatorWallet :: Wallet -> NodeClientState -> SimulatorWallet
    toSimulatorWallet simulatorWalletWallet walletState =
        SimulatorWallet
            { simulatorWalletWallet
            , simulatorWalletBalance =
                  walletStateBalance simulatorWalletWallet walletState
            }
    walletStateBalance :: Wallet -> NodeClientState -> Value
    walletStateBalance w =
        foldMap (txOutValue . txOutTxOut) .
        view (clientIndex . fundsAt (walletAddress w))
    toKeyWalletPair :: Wallet -> NodeClientState -> [(PubKey, Wallet)]
    toKeyWalletPair k _ = [(walletPubKey k, k)]

postProcessEvaluation :: TraceResult -> Either PlaygroundError EvaluationResult
postProcessEvaluation (resultBlockchain, emulatorLog, emulatorTrace, fundsDistribution, walletKeys) = do
    rollup <- first RollupError $ doAnnotateBlockchain resultBlockchain
    pure $
        EvaluationResult
            { resultBlockchain
            , resultRollup = rollup
            , emulatorLog
            , emulatorTrace
            , fundsDistribution
            , walletKeys = first pubKeyHash <$> walletKeys
            }

playgroundDecode ::
       FromJSON a => String -> ByteString -> Either PlaygroundError a
playgroundDecode expected input =
    first
        (\err ->
             JsonDecodingError
                 {expected, input = BSL.unpack input, decodingError = err}) $
    eitherDecode input

-- | Evaluate a JSON payload from the Playground frontend against a given contract schema.
stage ::
       forall s a.
       ( HasBlockchainActions s
       , Forall (Input s) FromJSON
       , Forall (Input s) Pretty
       , Forall (Output s) Pretty
       , Forall (Output s) Unconstrained1
       )
    => Contract s Text a
    -> BSL.ByteString
    -> BSL.ByteString
    -> Either PlaygroundError EvaluationResult
stage endpoints programJson simulatorWalletsJson = do
    simulationJson :: String <- playgroundDecode "String" programJson
    simulation :: [Expression] <-
        playgroundDecode "[Expression schema]" . BSL.pack $ simulationJson
    simulatorWallets :: [SimulatorWallet] <-
        playgroundDecode "[SimulatorWallet]" simulatorWalletsJson
    let allWallets = simulatorWalletWallet <$> simulatorWallets
    let (final, emulatorState) =
            runTraceWithDistribution
                (toInitialDistribution simulatorWallets)
                endpoints
                (buildSimulation allWallets (expressionToTrace <$> simulation))
    case final of
        Left err              -> throwError . OtherError . show $ err
        Right (_, traceState) -> analyzeEmulatorState traceState emulatorState

buildSimulation ::
       (MonadEmulator (TraceError e) m, HasBlockchainActions s)
    => [Wallet]
    -> [ContractTrace s e m a ()]
    -> ContractTrace s e m a ()
buildSimulation allWallets =
    sequence_ . afterEach (traverse_ triggerEvents allWallets)
  where
    afterEach a = foldMap (\x -> [x, a])

triggerEvents ::
       (MonadEmulator (TraceError e) m, HasBlockchainActions s)
    => Wallet
    -> ContractTrace s e m a ()
triggerEvents w = do
    handleBlockchainEvents w

toInitialDistribution :: [SimulatorWallet] -> Map Wallet Value
toInitialDistribution = Map.fromList . fmap (\(SimulatorWallet w v) -> (w, v))

expressionToTrace ::
       ( ContractRow s
       , HasAwaitSlot s
       , MonadEmulator (TraceError Text) m
       , Forall (Input s) FromJSON
       , Forall (Output s) Unconstrained1
       )
    => Expression
    -> ContractTrace s Text m a ()
expressionToTrace AddBlocks {blocks} = addBlocks (fromIntegral blocks)
expressionToTrace AddBlocksUntil {slot} = addBlocksUntil slot
expressionToTrace PayToWallet {sender, recipient, amount} =
    payToWallet sender recipient amount
expressionToTrace CallEndpoint { caller
                               , argumentValues = FunctionSchema { endpointDescription
                                                                 , argument = rawArgument
                                                                 }
                               } =
    let fromString (JSON.String string) =
            Just $ BSL.fromStrict $ Text.encodeUtf8 string
        fromString _ = Nothing
     in case fromString rawArgument of
            Just string ->
                case JSON.eitherDecode string of
                    Left errs ->
                        throwError . TContractError $
                        "Error extracting JSON from arguments. Expected an array of JSON strings. " <>
                        Text.pack (show errs)
                    Right argument -> do
                        event :: Event s <-
                            decodePayload endpointDescription $
                                JSON.object
                                    [ ( "tag"
                                      , JSON.String (Text.pack (getEndpointDescription endpointDescription)))
                                    , ("value", JSON.object [("unEndpointValue", argument)])
                                    ]
                        addNamedEvent (getEndpointDescription endpointDescription) caller event
            Nothing -> throwError . TContractError $ "Expected a String, but got: " <> Text.pack (show rawArgument)

decodePayload ::
       (MonadEmulator (TraceError Text) m, FromJSON r)
    => EndpointDescription
    -> JSON.Value
    -> ContractTrace s Text m a r
decodePayload endpointDescription value =
    case JSON.fromJSON value of
        JSON.Error err ->
            throwError . TContractError $
            "Error '" <> Text.pack err <> "' while decoding JSON arguments: " <>
            Text.pack (show value) <>
            "  for endpoint: " <>
            Text.pack (show endpointDescription)
        JSON.Success result -> pure result
