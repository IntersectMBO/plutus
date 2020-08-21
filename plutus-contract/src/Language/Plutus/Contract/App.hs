{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
-- | Run a Plutus contract as a servant application.
module Language.Plutus.Contract.App(
      run
    , runWithTraces
    , Wallet(..)
    ) where

import           Control.Monad                    (foldM_)
import           Data.Aeson                       (FromJSON, ToJSON)
import qualified Data.Aeson                       as Aeson
import qualified Data.ByteString.Lazy.Char8       as BSL
import           Data.Foldable                    (traverse_)
import qualified Data.Map                         as Map
import           Data.Row
import           Data.Row.Internal                (Unconstrained1)
import qualified Data.Text.IO                     as Text
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Schema  (Input, Output)
import           Language.Plutus.Contract.Servant (contractApp)
import           Language.Plutus.Contract.State   (ContractRequest (..), ContractResponse (..), initialiseContract,
                                                   insertAndUpdateContract)
import           Language.Plutus.Contract.Trace   (ContractTrace, EmulatorAction, TraceError, execTrace)
import qualified Network.Wai.Handler.Warp         as Warp
import           System.Environment               (getArgs)
import           Wallet.Emulator                  (Wallet (..))

import           Language.Plutus.Contract.IOTS    (IotsRow, IotsType, rowSchema)

-- | A number of constraints to ensure that 's' is the schema
--   of a contract whose inputs and outputs can be serialised to
--   JSON, and whose user-facing endpoints have 'IotsType' instances
type AppSchema s =
    ( AllUniqueLabels (Input s)
    , AllUniqueLabels (Output s)
    , Forall (Output s) ToJSON
    , Forall (Input (s .\\ BlockchainActions)) IotsType
    , AllUniqueLabels (Input (s .\\ BlockchainActions))
    , IotsRow (Input (s .\\ BlockchainActions))
    , Forall (Input (s .\\ BlockchainActions)) Unconstrained1
    , Forall (Input s) FromJSON
    , Forall (Input s) ToJSON )

-- | Run the contract as an HTTP server with servant/warp
run
    :: forall s e.
       ( AppSchema s, ToJSON e, Show e )
    => Contract s e () -> IO ()
run st = runWithTraces @s st []

-- | Run the contract as an HTTP server with servant/warp, and
--   print the 'Request' values for the given traces.
runWithTraces
    :: forall s e.
       ( AppSchema s, ToJSON e, Show e )
    => Contract s e ()
    -> [(String, (Wallet, ContractTrace s e (EmulatorAction (TraceError e)) () ()))]
    -> IO ()
runWithTraces con traces = do
    let mp = Map.fromList traces
    args <- getArgs
    case args of
        [] -> do
            let p = 8080
            putStrLn $ "Starting server on port " ++ show p
            Warp.run p (contractApp @s con)
        ["schema"] ->
            -- prints the schema for user-defined endpoints (ie. after
            -- removing the 'BlockchainActions' from the row)
            Text.putStrLn (rowSchema @(Input (s .\\ BlockchainActions)))
        ["trace", t] -> maybe (printTracesAndExit mp) (uncurry (printTrace con)) (Map.lookup t mp)
        _ -> printTracesAndExit mp

-- | Print a list of available traces
printTracesAndExit :: Map.Map String a -> IO ()
printTracesAndExit mp = do
    putStrLn "list of available traces (call with 'trace ${trace}')"
    traverse_ putStrLn (Map.keysSet mp)

-- | Run a trace on the mockchain and print the 'Request' JSON objects
--   for each intermediate state to stdout.
printTrace
    :: forall s e.
       ( Forall (Input s) ToJSON
       )
    => Contract s e ()
    -> Wallet
    -> ContractTrace s e (EmulatorAction (TraceError e)) () ()
    -> IO ()
printTrace con wllt ctr = do
    let events = Map.findWithDefault [] wllt $ execTrace con ctr
        go previous evt = do
            let st = newState previous
                newRequest = ContractRequest { oldState = st, event = evt }
            BSL.putStrLn (Aeson.encode newRequest)
            pure (insertAndUpdateContract con newRequest)

    initial <- pure (initialiseContract @s con)
    foldM_ go initial events
