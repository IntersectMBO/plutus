{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Playground.Interpreter.Util
    ( stage
    ) where

import           Control.Lens                    (view)
import           Control.Monad.Except            (throwError)
import qualified Control.Newtype.Generics        as Newtype
import           Data.Aeson                      (FromJSON, eitherDecode)
import qualified Data.Aeson                      as JSON
import           Data.Bifunctor                  (first)
import           Data.ByteString.Lazy            (ByteString)
import qualified Data.ByteString.Lazy.Char8      as BSL
import           Data.Foldable                   (traverse_)
import           Data.Map                        (Map)
import qualified Data.Map                        as Map
import           Data.Row                        (Forall)
import           Data.Text                       (Text)
import qualified Data.Text                       as Text
import qualified Data.Text.Encoding              as Text
import           Language.Haskell.Interpreter    (InterpreterResult (InterpreterResult), result, warnings)
import           Language.Plutus.Contract        (Contract, ContractRow, HasBlockchainActions)
import           Language.Plutus.Contract.Schema (Event, Input)
import           Language.Plutus.Contract.Trace  (ContractTrace, TraceError (ContractError), addBlocks, addBlocksUntil,
                                                  addEvent, handleBlockchainEvents, notifyInterestingAddresses,
                                                  notifySlot, payToWallet, runTraceWithDistribution)
import           Ledger                          (Blockchain, PubKey, TxOut (txOutValue), txOutTxOut)
import           Ledger.AddressMap               (fundsAt)
import           Ledger.Value                    (Value)
import qualified Ledger.Value                    as Value
import           Playground.Types                (ContractCall (AddBlocks, AddBlocksUntil, CallEndpoint, PayToWallet),
                                                  EndpointName, EvaluationResult (EvaluationResult), Expression,
                                                  FunctionSchema (FunctionSchema),
                                                  PlaygroundError (JsonDecodingError, OtherError, RollupError),
                                                  SimulatorWallet (SimulatorWallet), amount, argumentValues, arguments,
                                                  blocks, caller, decodingError, emulatorLog, endpointName, expected,
                                                  fundsDistribution, input, recipient, resultBlockchain, resultRollup,
                                                  sender, simulatorWalletBalance, simulatorWalletWallet, slot,
                                                  walletKeys)
import           Wallet.Emulator                 (MonadEmulator)
import           Wallet.Emulator.Chain           (ChainState (..))
import           Wallet.Emulator.NodeClient      (NodeClientState (..), clientIndex)
import           Wallet.Emulator.Types           (EmulatorEvent, EmulatorState (EmulatorState, _chainState, _emulatorLog, _walletClientStates),
                                                  Wallet)
import           Wallet.Emulator.Wallet          (walletAddress, walletPubKey)
import           Wallet.Rollup                   (doAnnotateBlockchain)

-- | Unfortunately any uncaught errors in the interpreter kill the
-- thread that is running it rather than returning the error. This
-- means we need to handle all expected errors in the expression we
-- are interpreting. This gets a little tricky because we have to
-- decode JSON inside the interpreter (since we don't have access to
-- it's type outside) so we need to wrap the @apply functions up in
-- something that can throw errors.
type TraceResult
     = (Blockchain, [EmulatorEvent], [SimulatorWallet], [(PubKey, Wallet)])

analyzeEmulatorState :: EmulatorState -> Either PlaygroundError EvaluationResult
analyzeEmulatorState EmulatorState { _chainState = ChainState { _chainNewestFirst
                                                              , _txPool
                                                              , _index
                                                              }
                                   , _walletClientStates
                                   , _emulatorLog
                                   } =
    postProcessEvaluation $
    InterpreterResult
        { warnings = []
        , result =
              ( _chainNewestFirst
              , _emulatorLog
              , fundsDistribution
              , Map.foldMapWithKey toKeyWalletPair _walletClientStates)
        }
  where
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

postProcessEvaluation ::
       InterpreterResult TraceResult -> Either PlaygroundError EvaluationResult
postProcessEvaluation (InterpreterResult _ (blockchain, emulatorLog, fundsDistribution, walletAddresses)) = do
    rollup <- first RollupError $ doAnnotateBlockchain blockchain
    pure $
        EvaluationResult
            { resultBlockchain = blockchain
            , resultRollup = rollup
            , emulatorLog = emulatorLog
            , fundsDistribution = fundsDistribution
            , walletKeys = walletAddresses
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
       (ContractRow s, HasBlockchainActions s, Forall (Input s) FromJSON)
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
        Left err -> throwError . OtherError . show $ err
        Right _  -> analyzeEmulatorState emulatorState

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
    notifyInterestingAddresses w
    notifySlot w

toInitialDistribution :: [SimulatorWallet] -> Map Wallet Value
toInitialDistribution = Map.fromList . fmap (\(SimulatorWallet w v) -> (w, v))

expressionToTrace ::
       ( ContractRow s
       , MonadEmulator (TraceError Text) m
       , Forall (Input s) FromJSON
       )
    => Expression
    -> ContractTrace s Text m a ()
expressionToTrace AddBlocks {blocks} = addBlocks (fromIntegral blocks)
expressionToTrace AddBlocksUntil {slot} = addBlocksUntil slot
expressionToTrace PayToWallet {sender, recipient, amount} =
    payToWallet sender recipient amount
expressionToTrace CallEndpoint { caller
                               , argumentValues = FunctionSchema { endpointName
                                                                 , arguments
                                                                 }
                               } =
    let fromString (JSON.String string) =
            Just $ BSL.fromStrict $ Text.encodeUtf8 string
        fromString _ = Nothing
     in case traverse fromString arguments of
            Just strings ->
                case traverse JSON.eitherDecode strings of
                    Left errs ->
                        throwError . ContractError $
                        "Error extracting JSON from arguments. Expected an array of JSON strings. " <>
                        Text.pack (show errs)
                    Right [argument] -> do
                        event :: Event s <-
                            decodePayload endpointName $
                            JSON.object
                                [ ( "tag"
                                  , JSON.String $ Newtype.unpack endpointName)
                                , ("value", argument)
                                ]
                        addEvent caller event
                    Right _ ->
                        throwError . ContractError $
                        "All contract endpoints take a single input argument. If you need more, use a tuple or record.\nExpected a singleton list, but got: " <>
                        Text.pack (show arguments)
            Nothing -> fail $ "Expected a [String], but got: " <> show arguments

decodePayload ::
       (MonadEmulator (TraceError Text) m, FromJSON r)
    => EndpointName
    -> JSON.Value
    -> ContractTrace s Text m a r
decodePayload endpointName value =
    case JSON.fromJSON value of
        JSON.Error err ->
            throwError . ContractError $
            "Error '" <> Text.pack err <> "' while decoding JSON arguments: " <>
            Text.pack (show value) <>
            "  for endpoint: " <>
            Text.pack (show endpointName)
        JSON.Success result -> pure result
