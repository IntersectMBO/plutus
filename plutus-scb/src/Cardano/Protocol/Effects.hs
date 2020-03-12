{-# LANGUAGE DataKinds #-}
module Cardano.Protocol.Effects where

import           Control.Concurrent
import           Control.Lens
import           Control.Monad.Freer        as Eff
import           Control.Monad.Freer.State
import           Control.Monad.Freer.Writer

import           Cardano.Node.Mock          (NodeServerEffects, runChainEffects)
import           Cardano.Node.Types         (AppState (..), chainState, initialFollowerState)
import           Cardano.Protocol.Type
import           Wallet.Emulator.Chain

wrapChainEffects :: MVar ChainState
                 -> Eff (NodeServerEffects IO) a
                 -> IO ([ChainEvent], a)
wrapChainEffects chState eff = do
  cs       <- takeMVar chState
  appState <- newMVar $ AppState cs [] initialFollowerState
  (events, result) <-
    runChainEffects appState eff
  as       <- takeMVar appState
  putMVar chState (as ^. chainState)
  pure (events, result)

runPureChainEffects :: ChainState
                    -> Eff '[ ChainEffect
                            , State ChainState
                            , Writer [ChainEvent] ] a
                    -> (a, ChainState)
runPureChainEffects oldState eff =
  let ((result, newState), _)
        = Eff.run $
          runWriter $
          runState oldState $
          handleChain eff
  in (result, newState)
