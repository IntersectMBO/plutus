-- | Run a plutus contract as a servant application
module Language.Plutus.Contract.App(
      run
    , runWithTraces
    , Wallet(..)
    ) where

import           Control.Monad                     (foldM_)
import qualified Data.Aeson                        as Aeson
import qualified Data.ByteString.Lazy.Char8        as BSL
import           Data.Foldable                     (traverse_)
import qualified Data.Map                          as Map
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Effects  (PlutusEffects)
import           Language.Plutus.Contract.Emulator (ContractTrace, EmulatorAction, execTrace)
import           Language.Plutus.Contract.Servant  (Request (..), Response (..), contractApp, initialResponse,
                                                    runUpdate)
import qualified Network.Wai.Handler.Warp          as Warp
import           System.Environment                (getArgs)
import           Wallet.Emulator                   (Wallet (..))

-- | Run the contract as an HTTP server with servant/warp
run :: Contract PlutusEffects () -> IO ()
run st = runWithTraces st []

-- | Run the contract as an HTTP server with servant/warp, and
--   print the 'Request' values for the given traces.
runWithTraces
    :: Contract PlutusEffects ()
    -> [(String, (Wallet, ContractTrace EmulatorAction () ()))]
    -> IO ()
runWithTraces con traces = do
    let mp = Map.fromList traces
    args <- getArgs
    case args of
        [] -> do
            let p = 8080
            putStrLn $ "Starting server on port " ++ show p
            Warp.run p (contractApp con)
        ["trace", t] -> maybe (printTracesAndExit mp) (uncurry (printTrace con)) (Map.lookup t mp)
        _ -> printTracesAndExit mp

-- | Print a list of available traces
printTracesAndExit :: Map.Map String a -> IO ()
printTracesAndExit mp = do
    putStrLn "list of available traces (call with 'trace ${trace}')"
    traverse_ putStrLn (Map.keysSet mp)

-- | Run a trace on the mockchain and print the 'Request' JSON objects
--   for each intermediate state to stdout.
printTrace :: Contract PlutusEffects () -> Wallet -> ContractTrace EmulatorAction () () -> IO ()
printTrace con wllt ctr = foldM_ go (initialResponse con) events where
    events = Map.findWithDefault [] wllt $ execTrace con ctr
    go previous evt = do
        let st = newState previous
            newRequest = Request { oldState = st, event = evt }
        BSL.putStrLn (Aeson.encode newRequest)
        either error pure (runUpdate con newRequest)
