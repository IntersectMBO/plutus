{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Playground.Interpreter.Util where

import           Control.Lens                    (to, view)
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
import           Language.Plutus.Contract.Trace  (ContractTrace, TraceError (ContractError, TraceAssertionError),
                                                  addBlocks, addEvent, handleBlockchainEvents,
                                                  notifyInterestingAddresses, notifySlot, payToWallet,
                                                  runTraceWithDistribution)
import           Ledger                          (Blockchain, PubKey, TxOut (txOutValue), toPublicKey, txOutTxOut)
import           Ledger.Value                    (Value)
import qualified Ledger.Value                    as Value
import           Playground.Types                (EvaluationResult (EvaluationResult, fundsDistribution, resultBlockchain, resultRollup, walletKeys),
                                                  Expression (AddBlocks, CallEndpoint, PayToWallet, arguments, blocks, destination, endpointName, source, value, wallet),
                                                  PlaygroundError (JsonDecodingError, OtherError, RollupError, decodingError, expected, input),
                                                  SimulatorWallet (SimulatorWallet), blocks, emulatorLog,
                                                  simulatorWalletBalance, simulatorWalletWallet)
import           Wallet.Emulator                 (MonadEmulator)
import           Wallet.Emulator.Types           (AssertionError (GenericAssertion), EmulatorEvent, EmulatorState (EmulatorState, _chainNewestFirst, _emulatorLog, _index, _txPool, _walletStates),
                                                  Wallet, WalletState, ownFunds, ownPrivateKey)
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
analyzeEmulatorState EmulatorState { _chainNewestFirst
                                   , _txPool
                                   , _walletStates
                                   , _index
                                   , _emulatorLog
                                   } =
    postProcessEvaluation $
    InterpreterResult
        { warnings = []
        , result =
              ( _chainNewestFirst
              , _emulatorLog
              , fundsDistribution
              , Map.foldMapWithKey toKeyWalletPair _walletStates)
        }
  where
    fundsDistribution :: [SimulatorWallet]
    fundsDistribution =
        filter (not . Value.isZero . simulatorWalletBalance) $
        Map.foldMapWithKey (\k v -> [toSimulatorWallet k v]) _walletStates
    toSimulatorWallet :: Wallet -> WalletState -> SimulatorWallet
    toSimulatorWallet simulatorWalletWallet walletState =
        SimulatorWallet
            { simulatorWalletWallet
            , simulatorWalletBalance = walletStateBalance walletState
            }
    walletStateBalance :: WalletState -> Value
    walletStateBalance = foldMap (txOutValue . txOutTxOut) . view ownFunds
    toKeyWalletPair :: Wallet -> WalletState -> [(PubKey, Wallet)]
    toKeyWalletPair k v = [(view (ownPrivateKey . to toPublicKey) v, k)]

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

stage ::
       forall s a.
       (ContractRow s, HasBlockchainActions s, Forall (Input s) FromJSON)
    => Contract s Text a
    -> BSL.ByteString
    -> BSL.ByteString
    -> Either PlaygroundError EvaluationResult
stage endpoints programJson simulatorWalletsJson = do
    simulationJson :: String <- playgroundDecode "String" programJson
    simulation :: [Expression s] <-
        playgroundDecode "[Expression schema]" $ BSL.pack simulationJson
    simulatorWallets :: [SimulatorWallet] <-
        playgroundDecode "[SimulatorWallet]" simulatorWalletsJson
    let allWallets = simulatorWalletWallet <$> simulatorWallets
    let (final, emulatorState) =
            runTraceWithDistribution
                (toInitialDistribution simulatorWallets)
                endpoints
                (buildSimulation allWallets (expressionToTrace <$> simulation))
    case final of
        Left (ContractError err)                          -> throwError . OtherError . Text.unpack $ err
        Left (TraceAssertionError (GenericAssertion err)) -> throwError . OtherError . Text.unpack $ err
        Right _                                           -> analyzeEmulatorState emulatorState

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
       (ContractRow s, MonadEmulator (TraceError Text) m, Forall (Input s) FromJSON)
    => Expression s
    -> ContractTrace s Text m a ()
expressionToTrace AddBlocks {blocks} = addBlocks (fromIntegral blocks)
expressionToTrace PayToWallet {source, destination, value} =
    payToWallet source destination value
expressionToTrace CallEndpoint {endpointName, wallet, arguments} =
    case arguments of
        JSON.String string ->
            let bytestring = BSL.fromStrict $ Text.encodeUtf8 string
             in case JSON.eitherDecode bytestring of
                    Left err ->
                        throwError . ContractError $
                        "Error extracting JSON from arguments. Expected a JSON string. " <>
                        Text.pack err
                    Right [value] ->
                        case JSON.fromJSON $
                             JSON.object
                                 [ ( "tag"
                                   , JSON.String $ Newtype.unpack endpointName)
                                 , ("value", value)
                                 ] of
                            JSON.Error err ->
                                throwError .
                                ContractError $
                                "Error '" <> Text.pack err <>
                                "' while decoding JSON arguments: " <>
                                Text.pack (show value) <>
                                "  for endpoint: " <>
                                Text.pack (show endpointName)
                            JSON.Success (event :: Event s) ->
                                addEvent wallet event
                    Right value ->
                        throwError .
                        ContractError $
                        "Expected a singleton list, but got: " <>
                        Text.pack (show value)
        _ -> fail $ "Expected a String, but got: " <> show arguments
