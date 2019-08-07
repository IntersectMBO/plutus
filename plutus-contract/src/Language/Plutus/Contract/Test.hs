{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
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
import           Control.Monad.Writer                  (MonadWriter (..), Writer, runWriter)
import           Data.Foldable                         (toList, traverse_)
import           Data.Functor.Contravariant            (Contravariant (..), Op(..))
import qualified Data.Map                              as Map
import           Data.Maybe                            (fromMaybe)
import           Data.Sequence                         (Seq)
import qualified Data.Sequence                         as Seq
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

newtype PredF f a = PredF { unPredF :: a -> f Bool }
    deriving Contravariant via (Op (f Bool))

instance Applicative f => Semigroup (PredF f a) where
    l <> r = PredF $ \a -> (&&) <$> unPredF l a <*> unPredF r a

instance Applicative f => Monoid (PredF f a) where
    mappend = (<>)
    mempty = PredF $ const (pure True)

type TracePredicate a = PredF (Writer (Seq String)) (InitialDistribution, ContractTraceResult a)

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
not = PredF . fmap (fmap Prelude.not) . unPredF

checkPredicate
    :: String
    -> Contract (ContractEffects '[]) a
    -> TracePredicate a
    -> ContractTrace EmulatorAction a ()
    -> TestTree
checkPredicate nm con predicate action =
    HUnit.testCaseSteps nm $ \step ->
        case runTrace con action of
            (Left err, _) ->
                HUnit.assertFailure $ "EmulatorAction failed. " ++ show err
            (Right (_, st), ms) -> do
                let dt = ContractTraceResult ms st
                    (result, emLog) = runWriter $ unPredF predicate (defaultDist, dt)
                if result then pure () else traverse_ step emLog
                HUnit.assertBool nm result

endpointAvailable :: Wallet -> String -> TracePredicate a
endpointAvailable w nm = PredF $ \(_, r) -> do
    let st = Hooks.activeEndpoints (hooks w r)
    if nm `Set.member` st
    then pure True
    else do
        tellSeq ["Active endpoints:", show st,  "missing endpoint:", nm]
        pure False

interestingAddress :: Wallet -> Address -> TracePredicate a
interestingAddress w addr = PredF $ \(_, r) -> do
    let hks = Hooks.addresses (hooks w r)
    if addr `Set.member` hks
    then pure True
    else do
        tellSeq ["Interesting addresses:", unlines (show <$> toList hks), "missing address:", show addr]
        pure False

tx :: Wallet -> (UnbalancedTx -> Bool) -> String -> TracePredicate a
tx w flt nm = PredF $ \(_, r) -> do
    let hks = Hooks.transactions (hooks w r)
    if any flt hks
    then pure True
    else do
        tellSeq ["Unbalanced transactions;", unlines (fmap show hks), "No transaction with '" <> nm <> "'"]
        pure False

walletState :: Wallet -> (EM.WalletState -> Bool) -> String -> TracePredicate a
walletState w flt nm = PredF $ \(_, r) -> do
    let ws = view (at w) $ EM._walletStates $  _ctrEmulatorState r
    case ws of
        Nothing -> do
            tellSeq ["Wallet state of '" <> show w <> "' not found"]
            pure False
        Just st ->
            if flt st
            then pure True
            else do
                tellSeq ["Wallet state of " <> show w <> ":", show st, "Fails '" <> nm <> "'"]
                pure False

walletWatchingAddress :: Wallet -> Address -> TracePredicate a
walletWatchingAddress w addr =
    let desc = "watching address " <> show addr in
    walletState w (Map.member addr . AM.values . view EM.addressMap) desc

assertEvents :: Wallet -> ([Event] -> Bool) -> String -> TracePredicate a
assertEvents w pr nm = PredF $ \(_, r) -> do
    let es = fmap toList (view (ctsEvents . at w) $ _ctrTraceState r)
    case es of
        Nothing -> do
            tellSeq ["Event log for '" <> show w <> "' not found"]
            pure False
        Just lg ->
            if pr lg
            then pure True
            else do
                tellSeq ["Event log for '" <> show w <> ":", unlines (fmap show lg), "Fails '" <> nm <> "'"]
                pure False

waitingForSlot :: Wallet -> Slot -> TracePredicate a
waitingForSlot w sl = PredF $ \(_, r) ->
    case Hooks.nextSlot (hooks w r) of
        Nothing -> do
            tellSeq [show w <> " not waiting for any slot notifications. Expected: " <>  show sl]
            pure False
        Just sl' ->
            if sl == sl'
            then pure True
            else do
                tellSeq [show w <> " waiting for " <> show sl', "Expected: " <> show sl]
                pure False

emulatorLog :: ([EmulatorEvent] -> Bool) -> String -> TracePredicate a
emulatorLog f nm = PredF $ \(_, r) ->
    let lg = EM._emulatorLog $ _ctrEmulatorState r in
    if f lg
    then pure True
    else do
        tellSeq ["Emulator log:", unlines (fmap show lg), "Fails '" <> nm <> "'"]
        pure False

anyTx :: Wallet -> TracePredicate a
anyTx w = tx w (const True) "anyTx"

assertHooks :: Wallet -> (Hooks -> Bool) -> String -> TracePredicate a
assertHooks w p nm = PredF $ \(_, rs) ->
    let hks = hooks w rs in
    if p hks
    then pure True
    else do
        tellSeq ["Hooks:", show hks, "Failed '" <> nm <> "'"]
        pure False

assertRecord :: Wallet -> (Record Event -> Bool) -> String -> TracePredicate a
assertRecord w p nm = PredF $ \(_, rs) ->
    case record w rs of
        Right r
            | p r -> pure True
            | otherwise -> do
                tellSeq ["Record: ", show r, "Failed '" <> nm <> "'"]
                pure False
        Left err -> do
            tellSeq ["Record failed with", show err, "in '" <> nm <> "'"]
            pure False

assertResult :: Wallet -> (Maybe a -> Bool) -> String -> TracePredicate a
assertResult w p nm = PredF $ \(_, rs) ->
    let evts = rs ^. ctrTraceState . ctsEvents . at w . folded . to toList
        con  = rs ^. ctrTraceState . ctsContract . to convertContract
        result = State.runResumable evts con
    in
        case fmap fst result of
            Left err
                | p Nothing -> pure True
                | otherwise -> do
                    tellSeq ["Resumable error", show err, "in '" <> nm <> "'"]
                    pure False
            Right (Left openRec)
                | p Nothing -> pure True
                | otherwise -> do
                    tellSeq ["Open record", show openRec, "in '" <> nm <> "'"]
                    pure False
            Right (Right (closedRec, a))
                | p (Just a) -> pure True
                | otherwise -> do
                    tellSeq ["Closed record", show closedRec, "failed with '" <> nm <> "'"]
                    pure False

walletFundsChange :: Wallet -> Value -> TracePredicate a
walletFundsChange w dlt = PredF $ \(initialDist, ContractTraceResult{_ctrEmulatorState = st}) ->
        let initialValue = foldMap Ada.toValue (Map.fromList initialDist ^. at w)
            finalValue   = fromMaybe mempty (EM.fundsDistribution st ^. at w)
        in if initialValue `V.plus` dlt == finalValue
        then pure True
        else do
            tellSeq ["Expected funds to change by", show dlt, "but they changed by", show (finalValue `V.minus` initialValue)]
            pure False

tellSeq :: MonadWriter (Seq a) m => [a] -> m ()
tellSeq = tell . Seq.fromList
