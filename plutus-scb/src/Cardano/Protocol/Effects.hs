{-# LANGUAGE DataKinds #-}
module Cardano.Protocol.Effects where

import           Control.Concurrent
import           Control.Lens
import           Control.Monad.Freer        as Eff
import           Control.Monad.Freer.State
import           Control.Monad.Freer.Writer

import           Cardano.Node.Mock          (NodeServerEffects, runChainEffects)
import           Cardano.Node.Types         (AppState (..), chainState)
import           Cardano.Protocol.Type
import qualified Wallet.Emulator.Chain      as EC

wrapChainEffects :: MVar ChainState
                 -> Eff (NodeServerEffects IO) a
                 -> IO ([EC.ChainEvent], a)
wrapChainEffects chState eff = do
  cs       <- takeMVar chState
  appState <- newMVar $ AppState (toEChainState cs) []
  (events, result) <-
    runChainEffects appState eff
  as       <- takeMVar appState
  putMVar chState (fromEChainState $ as ^. chainState)
  pure (events, result)

runPureChainEffects :: ChainState
                    -> Eff '[ EC.ChainEffect
                            , State EC.ChainState
                            , Writer [EC.ChainEvent] ] a
                    -> (a, ChainState)
runPureChainEffects oldState eff =
  let ((result, newState), _)
        = Eff.run $
          runWriter $
          runState (toEChainState oldState) $
          EC.handleChain eff
  in (result, fromEChainState newState)
