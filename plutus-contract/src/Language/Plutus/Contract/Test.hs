{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
-- | Testing contracts with HUnit and Tasty
module Language.Plutus.Contract.Test(
      module X
    , TracePredicate
    , Language.Plutus.Contract.Test.not
    , endpointAvailable
    , interestingAddress
    , assertOutcome
    , Outcome(..)
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
import           Data.Proxy                                      (Proxy(..))
import           Data.Row
import           Data.Sequence                         (Seq)
import qualified Data.Sequence                         as Seq
import qualified Data.Set                              as Set
import           GHC.TypeLits                          (Symbol, KnownSymbol, symbolVal)
import qualified Test.Tasty.HUnit                      as HUnit
import           Test.Tasty.Providers                  (TestTree)

import qualified Language.PlutusTx.Prelude             as P

import           Language.Plutus.Contract
import           Language.Plutus.Contract.Record       (Record)
import           Language.Plutus.Contract.Resumable    (ResumableError)
import qualified Language.Plutus.Contract.Resumable    as State
import           Language.Plutus.Contract.Tx           (UnbalancedTx)
import           Language.PlutusTx.Lattice

import qualified Language.Plutus.Contract.Effects.AwaitSlot      as AwaitSlot
import qualified Language.Plutus.Contract.Effects.ExposeEndpoint as Endpoints
import qualified Language.Plutus.Contract.Effects.WatchAddress   as WatchAddress
import qualified Language.Plutus.Contract.Effects.WriteTx        as WriteTx

import qualified Ledger.Ada                            as Ada
import qualified Ledger.AddressMap                     as AM
import           Ledger.Slot                           (Slot)
import           Ledger.Tx                             (Address)
import           Ledger.Value                          (Value)
import           Wallet.Emulator                       (EmulatorAction, EmulatorEvent, Wallet)
import qualified Wallet.Emulator                       as EM

import           Language.Plutus.Contract.Schema       (Event(..), Handlers(..), Input, Output)
import           Language.Plutus.Contract.Trace        as X

newtype PredF f a = PredF { unPredF :: a -> f Bool }
    deriving Contravariant via (Op (f Bool))

instance Applicative f => JoinSemiLattice (PredF f a) where
    l \/ r = PredF $ \a -> (\/) <$> unPredF l a <*> unPredF r a
instance Applicative f => MeetSemiLattice (PredF f a) where
    l /\ r = PredF $ \a -> (/\) <$> unPredF l a <*> unPredF r a

instance Applicative f => BoundedJoinSemiLattice (PredF f a) where
    bottom = PredF $ const (pure bottom)

instance Applicative f => BoundedMeetSemiLattice (PredF f a) where
    top = PredF $ const (pure top)

type TracePredicate s = PredF (Writer (Seq String)) (InitialDistribution, ContractTraceResult s)

hooks
    :: forall s.
       ( Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , AllUniqueLabels (Output s)
       )
    => Wallet
    -> ContractTraceResult s
    -> Handlers s
hooks w rs =
    let evts = rs ^. ctrTraceState . ctsEvents . at w . folded . to toList
        con  = rs ^. ctrTraceState . ctsContract
    in either (const mempty) id (State.execResumable evts con)

record 
    :: forall s.
       ( AllUniqueLabels (Output s)
       , Forall (Output s) Semigroup
       , Forall (Output s) Monoid
       )
    => Wallet 
    -> ContractTraceResult s
    -> Either ResumableError (Record (Event s))
record w rs =
    let evts = rs ^. ctrTraceState . ctsEvents . at w . folded . to toList
        con  = rs ^. ctrTraceState . ctsContract
    in fmap (fmap fst . fst) (State.runResumable evts con)

not :: TracePredicate s -> TracePredicate s
not = PredF . fmap (fmap Prelude.not) . unPredF

checkPredicate
    :: forall s.
       String
    -> Contract s ()
    -> TracePredicate s
    -> ContractTrace s EmulatorAction ()
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

endpointAvailable
    :: forall (l :: Symbol) s.
       ( HasType l Endpoints.ActiveEndpoints (Output s)
       , KnownSymbol l
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Wallet
    -> TracePredicate s
endpointAvailable w = PredF $ \(_, r) -> do
    if Endpoints.isActive @l @s (hooks w r)
    then pure True
    else do
        tellSeq ["missing endpoint:" ++ symbolVal (Proxy :: Proxy l)]
        pure False

interestingAddress
    :: forall s.
       ( WatchAddress.HasWatchAddress s )
    => Wallet
    -> Address
    -> TracePredicate s
interestingAddress w addr = PredF $ \(_, r) -> do
    let hks = WatchAddress.addresses (hooks w r)
    if addr `Set.member` hks
    then pure True
    else do
        tellSeq ["Interesting addresses:", unlines (show <$> toList hks), "missing address:", show addr]
        pure False

tx
    :: forall s.
       ( HasType "tx" WriteTx.PendingTransactions (Output s)
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup)
    => Wallet
    -> (UnbalancedTx -> Bool)
    -> String
    -> TracePredicate s
tx w flt nm = PredF $ \(_, r) -> do
    let hks = WriteTx.transactions (hooks w r)
    if any flt hks
    then pure True
    else do
        tellSeq ["Unbalanced transactions;", unlines (fmap show hks), "No transaction with '" <> nm <> "'"]
        pure False

walletState 
    :: forall s.
       Wallet 
    -> (EM.WalletState -> Bool) 
    -> String 
    -> TracePredicate s
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

walletWatchingAddress 
    :: forall s.
       Wallet
    -> Address
    -> TracePredicate s
walletWatchingAddress w addr =
    let desc = "watching address " <> show addr in
    walletState w (Map.member addr . AM.values . view EM.addressMap) desc

assertEvents 
    :: forall s.
       (Forall (Input s) Show)
    => Wallet
    -> ([Event s] -> Bool)
    -> String
    -> TracePredicate s
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

waitingForSlot
    :: forall s.
       ( HasType "slot" AwaitSlot.WaitingForSlot (Output s)
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Wallet
    -> Slot
    -> TracePredicate s
waitingForSlot w sl = PredF $ \(_, r) ->
    case AwaitSlot.nextSlot (hooks w r) of
        Nothing -> do
            tellSeq [show w <> " not waiting for any slot notifications. Expected: " <>  show sl]
            pure False
        Just sl' ->
            if sl == sl'
            then pure True
            else do
                tellSeq [show w <> " waiting for " <> show sl', "Expected: " <> show sl]
                pure False

emulatorLog
    :: forall s.
       ()
    => ([EmulatorEvent] -> Bool)
    -> String
    -> TracePredicate s
emulatorLog f nm = PredF $ \(_, r) ->
    let lg = EM._emulatorLog $ _ctrEmulatorState r in
    if f lg
    then pure True
    else do
        tellSeq ["Emulator log:", unlines (fmap show lg), "Fails '" <> nm <> "'"]
        pure False

anyTx
    :: forall s.
       ( HasType "tx" WriteTx.PendingTransactions (Output s)
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Wallet
    -> TracePredicate s
anyTx w = tx w (const True) "anyTx"

assertHooks 
    :: forall s.
       ( AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , Forall (Output s) Show
       )
    => Wallet
    -> (Handlers s -> Bool)
    -> String
    -> TracePredicate s
assertHooks w p nm = PredF $ \(_, rs) ->
    let hks = hooks w rs in
    if p hks
    then pure True
    else do
        tellSeq ["Handlers:", show hks, "Failed '" <> nm <> "'"]
        pure False

assertRecord 
    :: forall s.
       ( Forall (Input s) Show
       , Forall (Output s) Semigroup
       , Forall (Output s) Monoid
       , AllUniqueLabels (Output s)
       )
    => Wallet 
    -> (Record (Event s) -> Bool)
    -> String
    -> TracePredicate s
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

data Outcome = Done | NotDone
    deriving (Eq, Ord, Show)

assertOutcome
    :: forall s.
       ( Forall (Input s) Show
       , AllUniqueLabels (Output s)
       , Forall (Output s) Semigroup
       , Forall (Output s) Monoid
       )
    => Wallet
    -> (Outcome -> Bool)
    -> String
    -> TracePredicate s
assertOutcome w p nm = PredF $ \(_, rs) ->
    let evts = rs ^. ctrTraceState . ctsEvents . at w . folded . to toList
        con  = rs ^. ctrTraceState . ctsContract
        result = State.runResumable evts con
    in
        case fmap fst result of
            Left err
                | p NotDone -> pure True
                | otherwise -> do
                    tellSeq ["Resumable error", show err, "in '" <> nm <> "'"]
                    pure False
            Right (Left openRec)
                | p NotDone -> pure True
                | otherwise -> do
                    tellSeq ["Open record", show openRec, "in '" <> nm <> "'"]
                    pure False
            Right (Right (closedRec, _))
                | p Done -> pure True
                | otherwise -> do
                    tellSeq ["Closed record", show closedRec, "failed with '" <> nm <> "'"]
                    pure False

walletFundsChange
    :: forall s.
       ()
    => Wallet
    -> Value
    -> TracePredicate s
walletFundsChange w dlt = PredF $ \(initialDist, ContractTraceResult{_ctrEmulatorState = st}) ->
        let initialValue = foldMap Ada.toValue (Map.fromList initialDist ^. at w)
            finalValue   = fromMaybe mempty (EM.fundsDistribution st ^. at w)
        in if initialValue P.+ dlt == finalValue
        then pure True
        else do
            tellSeq ["Expected funds to change by", show dlt, "but they changed by", show (finalValue P.- initialValue)]
            pure False

tellSeq :: MonadWriter (Seq a) m => [a] -> m ()
tellSeq = tell . Seq.fromList
