{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
-- | Testing contracts with HUnit and Tasty
module Language.Plutus.Contract.Test(
      module X
    , TracePredicate
    , Language.Plutus.Contract.Test.not
    , endpointAvailable
    , interestingAddress
    , assertDone
    , assertNotDone
    , assertContractError
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
import           Data.Bifunctor                        (Bifunctor(..))
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

import           Language.Plutus.Contract.Record       (Record)
import           Language.Plutus.Contract.Request      (Contract(..), ContractError)
import           Language.Plutus.Contract.Resumable    (ResumableError)
import qualified Language.Plutus.Contract.Resumable    as State
import           Language.Plutus.Contract.Tx           (UnbalancedTx)
import           Language.PlutusTx.Lattice

import           Language.Plutus.Contract.Effects.AwaitSlot      (SlotSymbol)
import qualified Language.Plutus.Contract.Effects.AwaitSlot      as AwaitSlot
import qualified Language.Plutus.Contract.Effects.ExposeEndpoint as Endpoints
import qualified Language.Plutus.Contract.Effects.WatchAddress   as WatchAddress
import           Language.Plutus.Contract.Effects.WriteTx        (TxSymbol)
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

type TracePredicate s a = PredF (Writer (Seq String)) (InitialDistribution, ContractTraceResult s a)

hooks
    :: forall s a.
       ( Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , AllUniqueLabels (Output s)
       )
    => Wallet
    -> ContractTraceResult s a
    -> Handlers s
hooks w rs =
    let (evts, con) = contractEventsWallet rs w
    in either (const mempty) snd (State.runResumable evts (unContract con))

record 
    :: forall s a.
       ( AllUniqueLabels (Output s)
       , Forall (Output s) Semigroup
       , Forall (Output s) Monoid
       )
    => Wallet 
    -> ContractTraceResult s a
    -> Either (ResumableError ContractError) (Record (Event s))
record w rs =
    let (evts, con) = contractEventsWallet rs w
    in fmap (fmap fst . fst) (State.runResumable evts (unContract con))

not :: TracePredicate s a -> TracePredicate s a
not = PredF . fmap (fmap Prelude.not) . unPredF

checkPredicate
    :: forall s a.
       String
    -> Contract s a
    -> TracePredicate s a
    -> ContractTrace s EmulatorAction a ()
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
    :: forall (l :: Symbol) s a.
       ( HasType l Endpoints.ActiveEndpoints (Output s)
       , KnownSymbol l
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Wallet
    -> TracePredicate s a
endpointAvailable w = PredF $ \(_, r) -> do
    if Endpoints.isActive @l @s (hooks w r)
    then pure True
    else do
        tellSeq ["missing endpoint:" ++ symbolVal (Proxy :: Proxy l)]
        pure False

interestingAddress
    :: forall s a.
       ( WatchAddress.HasWatchAddress s )
    => Wallet
    -> Address
    -> TracePredicate s a
interestingAddress w addr = PredF $ \(_, r) -> do
    let hks = WatchAddress.addresses (hooks w r)
    if addr `Set.member` hks
    then pure True
    else do
        tellSeq ["Interesting addresses:", unlines (show <$> toList hks), "missing address:", show addr]
        pure False

tx
    :: forall s a.
       ( HasType TxSymbol WriteTx.PendingTransactions (Output s)
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup)
    => Wallet
    -> (UnbalancedTx -> Bool)
    -> String
    -> TracePredicate s a
tx w flt nm = PredF $ \(_, r) -> do
    let hks = WriteTx.transactions (hooks w r)
    if any flt hks
    then pure True
    else do
        tellSeq ["Unbalanced transactions;", unlines (fmap show hks), "No transaction with '" <> nm <> "'"]
        pure False

walletState 
    :: forall s a.
       Wallet 
    -> (EM.WalletState -> Bool) 
    -> String 
    -> TracePredicate s a
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
    :: forall s a.
       Wallet
    -> Address
    -> TracePredicate s a
walletWatchingAddress w addr =
    let desc = "watching address " <> show addr in
    walletState w (Map.member addr . AM.values . view EM.addressMap) desc

assertEvents 
    :: forall s a.
       (Forall (Input s) Show)
    => Wallet
    -> ([Event s] -> Bool)
    -> String
    -> TracePredicate s a
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
    :: forall s a.
       ( HasType SlotSymbol AwaitSlot.WaitingForSlot (Output s)
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Wallet
    -> Slot
    -> TracePredicate s a
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
    :: forall s a.
       ()
    => ([EmulatorEvent] -> Bool)
    -> String
    -> TracePredicate s a
emulatorLog f nm = PredF $ \(_, r) ->
    let lg = EM._emulatorLog $ _ctrEmulatorState r in
    if f lg
    then pure True
    else do
        tellSeq ["Emulator log:", unlines (fmap show lg), "Fails '" <> nm <> "'"]
        pure False

anyTx
    :: forall s a.
       ( HasType TxSymbol WriteTx.PendingTransactions (Output s)
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Wallet
    -> TracePredicate s a
anyTx w = tx w (const True) "anyTx"

assertHooks 
    :: forall s a.
       ( AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , Forall (Output s) Show
       )
    => Wallet
    -> (Handlers s -> Bool)
    -> String
    -> TracePredicate s a
assertHooks w p nm = PredF $ \(_, rs) ->
    let hks = hooks w rs in
    if p hks
    then pure True
    else do
        tellSeq ["Handlers:", show hks, "Failed '" <> nm <> "'"]
        pure False

assertRecord 
    :: forall s a.
       ( Forall (Input s) Show
       , Forall (Output s) Semigroup
       , Forall (Output s) Monoid
       , AllUniqueLabels (Output s)
       )
    => Wallet 
    -> (Record (Event s) -> Bool)
    -> String
    -> TracePredicate s a
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

data Outcome a = 
    Done a
    -- ^ The contract finished without errors and produced a result
    | NotDone
    -- ^ The contract is waiting for more input.
    | Error (ResumableError ContractError)
    -- ^ The contract failed with an error.
    deriving (Eq, Ord, Show)

-- | A 'TracePredicate' checking that the wallet's contract instance finished
--   without errors.
assertDone
    :: forall s a.
    ( Forall (Input s) Show
    , AllUniqueLabels (Output s)
    , Forall (Output s) Semigroup
    , Forall (Output s) Monoid
    , Forall (Output s) Show
    )
    => Wallet
    -> (a -> Bool)
    -> String
    -> TracePredicate s a
assertDone w pr = assertOutcome w (\case { Done a -> pr a; _ -> False})

-- | A 'TracePredicate' checking that the wallet's contract instance is 
--   waiting for input.
assertNotDone 
    :: forall s a.
    ( Forall (Input s) Show
    , AllUniqueLabels (Output s)
    , Forall (Output s) Semigroup
    , Forall (Output s) Monoid
    , Forall (Output s) Show
    )
    => Wallet
    -> String
    -> TracePredicate s a
assertNotDone w = assertOutcome w (\case { NotDone -> True; _ -> False})

-- | A 'TracePredicate' checking that the wallet's contract instance
--   failed with an error.
assertContractError
    :: forall s a.
    ( Forall (Input s) Show
    , AllUniqueLabels (Output s)
    , Forall (Output s) Semigroup
    , Forall (Output s) Monoid
    , Forall (Output s) Show
    )
    => Wallet
    -> ContractError
    -> String
    -> TracePredicate s a
assertContractError w err =
    assertOutcome w (\case { Error (State.OtherError err') -> err' == err; _ -> False })

assertOutcome
    :: forall s a.
       ( Forall (Input s) Show
       , AllUniqueLabels (Output s)
       , Forall (Output s) Semigroup
       , Forall (Output s) Monoid
       , Forall (Output s) Show
       )
    => Wallet
    -> (Outcome a -> Bool)
    -> String
    -> TracePredicate s a
assertOutcome w p nm = PredF $ \(_, rs) ->
    let (evts, con) = contractEventsWallet rs w
        result = State.runResumable evts (unContract con)
    in
        case fmap fst result of
            Left err
                | p (Error err) -> pure True
                | otherwise -> do
                    tellSeq ["Resumable error", show err, "in '" <> nm <> "'"]
                    pure False
            Right (Left openRec)
                | p NotDone -> pure True
                | otherwise -> do
                    tellSeq ["Open record", show openRec, "in '" <> nm <> "'"]
                    tellSeq [show (fmap (first (fmap fst)) result)]
                    pure False
            Right (Right closedRec)
                | p (Done (snd closedRec)) -> pure True
                | otherwise -> do
                    tellSeq 
                        [ "Closed record"
                        , show (fst closedRec)
                        , "failed with '" <> nm <> "'"]
                    pure False

contractEventsWallet 
    :: ContractTraceResult s a
    -> Wallet
    -> ([Event s], Contract s a)
contractEventsWallet rs w = 
    let evts = rs ^. ctrTraceState . ctsEvents . at w . folded . to toList
        con  = rs ^. ctrTraceState . ctsContract
    in (evts, con)

walletFundsChange
    :: forall s a.
       ()
    => Wallet
    -> Value
    -> TracePredicate s a
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
