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
import           Data.Functor.Const               (Const (..))
import qualified Data.Map                         as Map
import           Data.Row
import           Data.Row.Internal                (Unconstrained1)
import           Data.Sequence                    (Seq)
import           Data.Text                        (Text)
import qualified Data.Text.IO                     as Text
import           Language.Plutus.Contract
import           Language.Plutus.Contract.Schema  (Input, Output)
import           Language.Plutus.Contract.Servant (Request (..), Response (..), contractApp, initialResponse, runUpdate)
import           Language.Plutus.Contract.Trace   (ContractTrace, EmulatorAction, execTrace)
import qualified Network.Wai.Handler.Warp         as Warp
import           System.Environment               (getArgs)
import           Wallet.Emulator                  (Wallet (..))

import           Language.Plutus.Contract.IOTS    (IotsType, schemaMap)

-- | A number of constraints to ensure that 's' is the schema
--   of a contract whose inputs and outputs can be serialised to
--   JSON, and whose user-facing endpoints have 'IotsType' instances
type AppSchema s =
    ( AllUniqueLabels (Input s)
    , AllUniqueLabels (Output s)
    , Forall (Output s) Monoid
    , Forall (Output s) Semigroup
    , Forall (Output s) ToJSON
    , Forall (Input (s .\\ BlockchainActions)) IotsType
    , AllUniqueLabels (Input (s .\\ BlockchainActions))
    , Forall (Input (s .\\ BlockchainActions)) Unconstrained1
    , Forall (Input s) FromJSON
    , Forall (Input s) ToJSON )

-- | Run the contract as an HTTP server with servant/warp
run
    :: forall s.
       ( AppSchema s )
    => Contract s () -> IO ()
run st = runWithTraces @s st []

-- | Run the contract as an HTTP server with servant/warp, and
--   print the 'Request' values for the given traces.
runWithTraces
    :: forall s.
       ( AppSchema s )
    => Contract s ()
    -> [(String, (Wallet, ContractTrace s EmulatorAction () ()))]
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
            -- This has two reasons.
            -- 1. Many of the ledger-specific types used in 'BlockchainActions'
            --    don't have 'IotsType' instances yet
            --    TODO: Add 'IotsType' instances for 'Ledger.Tx.Tx' and related
            --          types
            -- 2. It's not clear whether the app platform expects the
            --    'BlockchainActions' to be included in the schema. (Including
            --    them would make sense from our perspective since they work
            --    exactly the same as user-defined endpoints, but if we do
            --    include them then the app platform needs to filter them out
            --    so that they're not displayed in the UI.
            --    TODO: Decide whether 'BlockchainActions' should be included.
            printSchemaAndExit (getConst $ schemaMap @(Input (s .\\ BlockchainActions)))
        ["trace", t] -> maybe (printTracesAndExit mp) (uncurry (printTrace con)) (Map.lookup t mp)
        _ -> printTracesAndExit mp

-- | Print the schema and exit
printSchemaAndExit :: Seq Text -> IO ()
printSchemaAndExit = traverse_ printSchema where
    printSchema = Text.putStrLn

-- | Print a list of available traces
printTracesAndExit :: Map.Map String a -> IO ()
printTracesAndExit mp = do
    putStrLn "list of available traces (call with 'trace ${trace}')"
    traverse_ putStrLn (Map.keysSet mp)

-- | Run a trace on the mockchain and print the 'Request' JSON objects
--   for each intermediate state to stdout.
printTrace
    :: forall s.
       ( AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , Forall (Input s) ToJSON )
    => Contract s ()
    -> Wallet
    -> ContractTrace s EmulatorAction () ()
    -> IO ()
printTrace con wllt ctr = do
    let events = Map.findWithDefault [] wllt $ execTrace con ctr
        go previous evt = do
            let st = newState previous
                newRequest = Request { oldState = st, event = evt }
            BSL.putStrLn (Aeson.encode newRequest)
            either (error . show) pure (runUpdate con newRequest)

    initial <- either (error . show) pure (initialResponse @s con)
    foldM_ go initial events

