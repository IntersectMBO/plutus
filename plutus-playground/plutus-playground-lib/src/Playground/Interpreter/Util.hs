{-# LANGUAGE FlexibleContexts #-}

module Playground.Interpreter.Util where

import           Control.Lens               (view)
import           Control.Monad.Error.Class  (MonadError, throwError)
import           Data.Aeson                 (FromJSON)
import qualified Data.Aeson                 as JSON
import qualified Data.ByteString.Lazy.Char8 as BSL
import           Data.Foldable              (foldl')
import qualified Data.Map                   as Map
import qualified Data.Set                   as Set
import qualified Data.Typeable              as T
import qualified Ledger.Ada                 as Ada
import           Ledger.Types               (Blockchain, PubKey (PubKey), Tx, TxOutOf (txOutValue))
import           Ledger.Value               (Value)
import qualified Ledger.Value               as Value
import           Playground.API             (PlaygroundError (OtherError))
import           Wallet.Emulator.Types      (EmulatorEvent, EmulatorState (_chainNewestFirst, _emulatorLog), MockWallet,
                                             Trace, Wallet (Wallet), ownFunds, processPending, runTraceTxPool,
                                             walletStates, walletsNotifyBlock)
import           Wallet.Generators          (GeneratorModel (GeneratorModel))
import qualified Wallet.Generators          as Gen

-- | Unfortunately any uncaught errors in the interpreter kill the thread that is running it rather than returning the error. This means we need to handle all expected errors in the expression we are interpreting. This gets a little tricky because we have to decode JSON inside the interpreter (since we don't have access to it's type outside) so we need to wrap the @apply functions up in something that can throw errors.
runTrace ::
     [(Wallet, Int)]
  -> [Either PlaygroundError (Trace MockWallet [Tx])]
  -> Either PlaygroundError (Blockchain, [EmulatorEvent], [(Wallet, Value)])
runTrace wallets actions =
  let walletToBalance (Wallet i, v) = (PubKey i, Ada.adaValueOf v)
      initialBalance = Map.fromList $ fmap walletToBalance wallets
      pubKeys = Set.fromList $ fmap (\(Wallet i, _) -> PubKey i) wallets
      eActions = sequence actions
   in case eActions of
        Left e -> Left e
        Right actions' ->
          let notifyAll =
                processPending >>=
                walletsNotifyBlock (Wallet <$> [1 .. length wallets])
              action = notifyAll >> sequence actions'
              (initialTx, _) =
                Gen.genInitialTransaction $
                GeneratorModel initialBalance pubKeys
              (eRes, newState) = runTraceTxPool [initialTx] action
              blockchain = _chainNewestFirst newState
              emulatorLog = _emulatorLog newState
              fundsDistribution =
                Map.map (foldl' Value.plus Value.zero . fmap txOutValue . view ownFunds) .
                view walletStates $
                newState
           in case eRes of
                Right _ ->
                  Right (blockchain, emulatorLog, Map.toList fundsDistribution)
                Left e -> Left . OtherError . show $ e

-- | This will throw an exception if it cannot decode the json however it should
--   never do this as long as it is only called in places where we have already
--   decoded and encoded the value since it came from an HTTP API call
{-# ANN decode' ("HLint: ignore" :: String) #-}

decode' :: (FromJSON a, T.Typeable a) => String -> a
decode' v =
  let x = JSON.eitherDecode . BSL.pack $ v
   in case x of
        Right a -> a
        Left e ->
          error $
          "couldn't decode " ++
          v ++ " :: " ++ show (T.typeOf x) ++ " (" ++ show e ++ ")"

decode ::
     (FromJSON a, T.Typeable a, MonadError PlaygroundError m) => String -> m a
decode v =
  let x = JSON.eitherDecode . BSL.pack $ v
   in case x of
        Right a -> pure a
        Left e ->
          throwError . OtherError $
          "couldn't decode " ++
          v ++ " :: " ++ show (T.typeOf x) ++ " (" ++ show e ++ ")"

{-# ANN module ("HLint: ignore Reduce duplication" :: String) #-}

apply ::
     (MonadError PlaygroundError m)
  => a
  -> m a
apply = pure

apply1 ::
     (T.Typeable a, FromJSON a, MonadError PlaygroundError m)
  => (a -> b)
  -> String
  -> m b
apply1 fun v = fun <$> decode v

apply2 ::
     ( T.Typeable a
     , FromJSON a
     , T.Typeable b
     , FromJSON b
     , MonadError PlaygroundError m
     )
  => (a -> b -> c)
  -> String
  -> String
  -> m c
apply2 fun a b = do
  a' <- decode a
  b' <- decode b
  pure $ fun a' b'

apply3 ::
     ( T.Typeable a
     , T.Typeable a
     , FromJSON a
     , T.Typeable b
     , FromJSON b
     , T.Typeable c
     , FromJSON c
     , MonadError PlaygroundError m
     )
  => (a -> b -> c -> d)
  -> String
  -> String
  -> String
  -> m d
apply3 fun a b c = do
  a' <- decode a
  b' <- decode b
  c' <- decode c
  pure $ fun a' b' c'

apply4 ::
     ( T.Typeable a
     , FromJSON a
     , T.Typeable b
     , FromJSON b
     , T.Typeable c
     , FromJSON c
     , T.Typeable d
     , FromJSON d
     , MonadError PlaygroundError m
     )
  => (a -> b -> c -> d -> e)
  -> String
  -> String
  -> String
  -> String
  -> m e
apply4 fun a b c d = do
  a' <- decode a
  b' <- decode b
  c' <- decode c
  d' <- decode d
  pure $ fun a' b' c' d'

apply5 ::
     ( T.Typeable a
     , FromJSON a
     , T.Typeable b
     , FromJSON b
     , T.Typeable c
     , FromJSON c
     , T.Typeable d
     , FromJSON d
     , T.Typeable e
     , FromJSON e
     , MonadError PlaygroundError m
     )
  => (a -> b -> c -> d -> e -> f)
  -> String
  -> String
  -> String
  -> String
  -> String
  -> m f
apply5 fun a b c d e = do
  a' <- decode a
  b' <- decode b
  c' <- decode c
  d' <- decode d
  e' <- decode e
  pure $ fun a' b' c' d' e'

apply6 ::
     ( T.Typeable a
     , FromJSON a
     , T.Typeable b
     , FromJSON b
     , T.Typeable c
     , FromJSON c
     , T.Typeable d
     , FromJSON d
     , T.Typeable e
     , FromJSON e
     , T.Typeable f
     , FromJSON f
     , MonadError PlaygroundError m
     )
  => (a -> b -> c -> d -> e -> f -> g)
  -> String
  -> String
  -> String
  -> String
  -> String
  -> String
  -> m g
apply6 fun a b c d e f = do
  a' <- decode a
  b' <- decode b
  c' <- decode c
  d' <- decode d
  e' <- decode e
  f' <- decode f
  pure $ fun a' b' c' d' e' f'

apply7 ::
     ( T.Typeable a
     , FromJSON a
     , T.Typeable b
     , FromJSON b
     , T.Typeable c
     , FromJSON c
     , T.Typeable d
     , FromJSON d
     , T.Typeable e
     , FromJSON e
     , T.Typeable f
     , FromJSON f
     , T.Typeable g
     , FromJSON g
     , MonadError PlaygroundError m
     )
  => (a -> b -> c -> d -> e -> f -> g -> h)
  -> String
  -> String
  -> String
  -> String
  -> String
  -> String
  -> String
  -> m h
apply7 fun a b c d e f g = do
  a' <- decode a
  b' <- decode b
  c' <- decode c
  d' <- decode d
  e' <- decode e
  f' <- decode f
  g' <- decode g
  pure $ fun a' b' c' d' e' f' g'
