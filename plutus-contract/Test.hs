{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
module Test where

import           Control.Lens
import           Control.Monad                          (forM, forever, void)
import           Control.Monad.Error.Lens
import           Control.Monad.Except                   (catchError, throwError)
import           Control.Monad.Freer                    (Eff)
import           Control.Monad.Freer.Extras.Log         (LogLevel (..))
import qualified Control.Monad.Freer.Extras.Log         as Log
import           Test.Tasty

import           Ledger                                 (Address, PubKey, Slot)
import qualified Ledger                                 as Ledger
import qualified Ledger.Ada                             as Ada
import qualified Ledger.Constraints                     as Constraints
import qualified Ledger.Crypto                          as Crypto
import           Plutus.Contract                        as Con
import qualified Plutus.Contract.State                  as State
import           Plutus.Contract.Test
import           Plutus.Contract.Types                  (ResumableResult (..), responses)
import           Plutus.Contract.Util                   (loopM)
import qualified Plutus.Trace                           as Trace
import           Plutus.Trace.Emulator                  (ContractInstanceTag, Emulator, EmulatorTrace, activateContract,
                                                         activeEndpoints, callEndpoint)
import           Plutus.Trace.Emulator.Types            (ContractInstanceLog (..), ContractInstanceMsg (..),
                                                         ContractInstanceState (..), UserThreadMsg (..))
import qualified PlutusTx                               as PlutusTx
import           PlutusTx.Lattice
import           Prelude                                hiding (not)
import qualified Prelude                                as P
import qualified Wallet.Emulator                        as EM

import qualified Plutus.Contract.Effects.AwaitSlot      as AwaitSlot
import           Plutus.Contract.Effects.ExposeEndpoint (ActiveEndpoint (..))
import qualified Plutus.Contract.Effects.ExposeEndpoint as Endpoint
import           Plutus.Contract.Resumable              (IterationID, Response (..))
import           Plutus.Contract.Trace.RequestHandler   (maybeToHandler)

type Schema =
    BlockchainActions
        .\/ Endpoint "1" Int
        .\/ Endpoint "2" Int
        .\/ Endpoint "3" Int
        .\/ Endpoint "4" Int
        .\/ Endpoint "ep" ()
        .\/ Endpoint "5" [ActiveEndpoint]

loopCheckpointContract :: Contract () Schema ContractError Int
loopCheckpointContract = do
    k <- endpoint @"2" @Int
    flip checkpointLoop (0 :: Int) $ \counter -> do
        vl1 <- endpoint @"1" @Int
        vl2 <- endpoint @"1" @Int
        let newVal = counter + vl1 + vl2
        if newVal > 3
            then pure (Left $ newVal + k)
            else pure (Right newVal)

initial :: _
initial = State.initialiseContract loopCheckpointContract

upd :: _
upd = State.insertAndUpdateContract loopCheckpointContract

initial' = upd State.ContractRequest{State.oldState = State.newState initial, State.event = Response{rspRqID = 1, rspItID = 1, rspResponse = Endpoint.event @"2" 5}}

call :: IterationID -> Int -> _
call it i oldState =
    let r = upd State.ContractRequest{State.oldState, State.event = Response{rspRqID = 1, rspItID = it, rspResponse = Endpoint.event @"1" i}}
    in (State.newState r, State.hooks r)

terminate = snd $ call 5 1 $ fst $ call 4 1 $ fst $ call 3 1 $ fst $ call 2 1 $ State.newState initial'


nonTerminate = snd $ call 4 1 $ fst $ call 3 1 $ fst $ call 2 1 $ State.newState initial'
