module Main where

import           Data.Functor                   (void)
import           Data.Map.Lazy                  as Map

import           Control.Lens

import           System.Environment

import           Cardano.Protocol.Server
import           Cardano.Protocol.Type
import           Language.Plutus.Contract.Trace (InitialDistribution, defaultDist)
import           Wallet.Emulator                as EM
import           Wallet.Emulator.Chain
import           Wallet.Emulator.MultiAgent     as MA

initialChainState :: InitialDistribution -> ChainState
initialChainState =
      view EM.chainState
    . MA.emulatorStateInitialDist
    . Map.mapKeys EM.walletPubKey

main :: IO ()
main = do
    [sockAddr] <- getArgs
    void $ startServerNode sockAddr (initialChainState defaultDist)
