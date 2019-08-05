{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
-- | Testing contracts with HUnit and Tasty
module Language.Plutus.Contract.Test(
      module X
    , TracePredicate
    , Language.Plutus.Contract.Test.not
    , endpointAvailable
    , interestingAddress
    , assertResult
    , assertHooks
    , assertRecord
    , tx
    , anyTx
    , assertEvents
    , walletFundsChange
    , waitingForSlot
    , walletState
    , walletWatchingAddress
    , emulatorLog
    -- * Checking predicates
    , checkPredicate
    ) where

import           Control.Lens                          (at, folded, to, view, (^.))
import           Data.Foldable                         (toList)
import           Data.Functor.Contravariant            (Predicate (..))
import qualified Data.Map                              as Map
import           Data.Maybe                            (fromMaybe)
import qualified Data.Set                              as Set
import qualified Test.Tasty.HUnit                      as HUnit
import           Test.Tasty.Providers                  (TestTree)

import           Language.Plutus.Contract              (Contract, convertContract)
import           Language.Plutus.Contract.Effects      (ContractEffects)
import           Language.Plutus.Contract.Prompt.Event (Event)
import           Language.Plutus.Contract.Prompt.Hooks (Hooks (..))
import qualified Language.Plutus.Contract.Prompt.Hooks as Hooks
import           Language.Plutus.Contract.Record       (Record)
import           Language.Plutus.Contract.Resumable    (ResumableError)
import qualified Language.Plutus.Contract.Resumable    as State
import           Language.Plutus.Contract.Tx           (UnbalancedTx)

import qualified Ledger.Ada                            as Ada
import qualified Ledger.AddressMap                     as AM
import           Ledger.Slot                           (Slot)
import           Ledger.Tx                             (Address)
import           Ledger.Value                          (Value)
import qualified Ledger.Value                          as V
import           Wallet.Emulator                       (EmulatorAction, EmulatorEvent, Wallet)
import qualified Wallet.Emulator                       as EM

import           Language.Plutus.Contract.Trace        as X

type TracePredicate a = InitialDistribution -> Predicate (ContractTraceResult a)

hooks :: Wallet -> ContractTraceResult a -> Hooks
hooks w rs =
    let evts = rs ^. ctrTraceState . ctsEvents . at w . folded . to toList
        con  = rs ^. ctrTraceState . ctsContract . to convertContract
    in either (const mempty) id (State.execResumable evts con)

record :: Wallet -> ContractTraceResult a -> Either ResumableError (Record Event)
record w rs =
    let evts = rs ^. ctrTraceState . ctsEvents . at w . folded . to toList
        con  = rs ^. ctrTraceState . ctsContract . to convertContract
    in fmap (fmap fst . fst) (State.runResumable evts con)

not :: TracePredicate a -> TracePredicate a
not p a = Predicate $ \b -> Prelude.not (getPredicate (p a) b)

checkPredicate
    :: String
    -> Contract (ContractEffects '[]) a
    -> TracePredicate a
    -> ContractTrace EmulatorAction a ()
    -> TestTree
checkPredicate nm con predicate action =
    HUnit.testCase nm $
        case runTrace con action of
            (Left err, _) ->
                HUnit.assertFailure $ "EmulatorAction failed. " ++ show err
            (Right (_, st), ms) ->
                let dt = ContractTraceResult ms st in
                HUnit.assertBool nm (getPredicate (predicate defaultDist) dt)

endpointAvailable :: Wallet -> String -> TracePredicate a
endpointAvailable w nm _ = Predicate $ \r ->
    nm `Set.member` Hooks.activeEndpoints (hooks w r)

interestingAddress :: Wallet -> Address -> TracePredicate a
interestingAddress w addr _ = Predicate $ \r ->
        addr `Set.member` Hooks.addresses (hooks w r)

tx :: Wallet -> (UnbalancedTx -> Bool) -> TracePredicate a
tx w flt _ = Predicate $ \r ->
    any flt (Hooks.transactions (hooks w r))

walletState :: Wallet -> (EM.WalletState -> Bool) -> TracePredicate a
walletState w flt _ = Predicate $ \r ->
    maybe False flt $ view (at w) $ EM._walletStates $  _ctrEmulatorState r

walletWatchingAddress :: Wallet -> Address -> TracePredicate a
walletWatchingAddress w addr = walletState w (Map.member addr . AM.values . view EM.addressMap)

assertEvents :: Wallet -> ([Event] -> Bool) -> TracePredicate a
assertEvents w pr _ = Predicate $ \r ->
    pr. maybe [] toList . view (ctsEvents . at w) $ _ctrTraceState r

waitingForSlot :: Wallet -> Slot -> TracePredicate a
waitingForSlot w sl _ = Predicate $ \r ->
    Just sl == Hooks.nextSlot (hooks w r)

emulatorLog :: ([EmulatorEvent] -> Bool) -> TracePredicate a
emulatorLog f _ = Predicate $ \r ->
    f $ EM._emulatorLog $ _ctrEmulatorState r

anyTx :: Wallet -> TracePredicate a
anyTx w = tx w (const True)

assertHooks :: Wallet -> (Hooks -> Bool) -> TracePredicate a
assertHooks w p _ = Predicate $ \rs -> p (hooks w rs)

assertRecord :: Wallet -> (Record Event -> Bool) -> TracePredicate a
assertRecord w p _ = Predicate $ \rs ->
    either (const False) p (record w rs)

assertResult :: Wallet -> (Maybe a -> Bool) -> TracePredicate a
assertResult w p _ = Predicate $ \rs ->
    let evts = rs ^. ctrTraceState . ctsEvents . at w . folded . to toList
        con  = rs ^. ctrTraceState . ctsContract . to convertContract
        result = either (const Nothing) (either (const Nothing) (Just . snd) . fst) (State.runResumable evts con)
    in p result

walletFundsChange :: Wallet -> Value -> TracePredicate a
walletFundsChange w dlt initialDist = Predicate $
    \ContractTraceResult{_ctrEmulatorState = st} ->
        let initialValue = foldMap Ada.toValue (Map.fromList initialDist ^. at w)
            finalValue   = fromMaybe mempty (EM.fundsDistribution st ^. at w)
        in initialValue `V.plus` dlt == finalValue
