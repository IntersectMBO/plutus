{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
-- | Testing contracts with HUnit and Tasty
module Language.Plutus.Contract.Test(
      module X
    , TracePredicate
    , PredF(..)
    , Language.Plutus.Contract.Test.not
    , endpointAvailable
    , interestingAddress
    , assertDone
    , assertNotDone
    , assertContractError
    , assertOutcome
    , assertNoFailedTransactions
    , assertFailedTransaction
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
    , fundsAtAddress
    -- * Checking predicates
    , checkPredicate
    , renderTraceContext
    ) where

import           Control.Lens                                    (at, view, (^.))
import           Control.Monad                                   (unless)
import           Control.Monad.Writer                            (MonadWriter (..), Writer, runWriter)
import           Data.Foldable                                   (fold, toList)
import           Data.Functor.Contravariant                      (Contravariant (..), Op (..))
import qualified Data.Map                                        as Map
import           Data.Maybe                                      (fromMaybe, mapMaybe)
import           Data.Proxy                                      (Proxy (..))
import           Data.Row                                        (AllUniqueLabels, Forall, HasType)
import qualified Data.Set                                        as Set
import           Data.String                                     (IsString (..))
import qualified Data.Text                                       as Text
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.Text           (renderStrict)
import           Data.Void
import           GHC.TypeLits                                    (KnownSymbol, Symbol, symbolVal)
import qualified Test.Tasty.HUnit                                as HUnit
import           Test.Tasty.Providers                            (TestTree)

import qualified Language.PlutusTx.Prelude                       as P

import           Language.Plutus.Contract.Record                 (Record)
import qualified Language.Plutus.Contract.Record                 as Rec
import           Language.Plutus.Contract.Request                (Contract (..))
import           Language.Plutus.Contract.Resumable              (ResumableError)
import qualified Language.Plutus.Contract.Resumable              as State
import           Language.PlutusTx.Lattice
import           Ledger.Constraints.OffChain                     (UnbalancedTx)

import           Language.Plutus.Contract.Effects.AwaitSlot      (SlotSymbol)
import qualified Language.Plutus.Contract.Effects.AwaitSlot      as AwaitSlot
import qualified Language.Plutus.Contract.Effects.ExposeEndpoint as Endpoints
import qualified Language.Plutus.Contract.Effects.WatchAddress   as WatchAddress
import           Language.Plutus.Contract.Effects.WriteTx        (TxSymbol)
import qualified Language.Plutus.Contract.Effects.WriteTx        as WriteTx

import           Ledger.Address                                  (Address)
import qualified Ledger.AddressMap                               as AM
import           Ledger.Index                                    (ValidationError)
import           Ledger.Slot                                     (Slot)
import           Ledger.TxId                                     (TxId)
import           Ledger.Value                                    (Value)
import           Wallet.Emulator                                 (EmulatorAction, EmulatorEvent, Wallet)
import qualified Wallet.Emulator                                 as EM
import qualified Wallet.Emulator.Chain                           as EM
import qualified Wallet.Emulator.NodeClient                      as EM

import           Language.Plutus.Contract.Schema                 (Event (..), Handlers (..), Input, Output)
import           Language.Plutus.Contract.Trace                  as X

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

type TracePredicate s e a = PredF (Writer (Doc Void)) (InitialDistribution, ContractTraceResult s e a)

hooks
    :: forall s e a.
       ( Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , AllUniqueLabels (Output s)
       )
    => Wallet
    -> ContractTraceResult s e a
    -> Handlers s
hooks w rs =
    let (evts, con) = contractEventsWallet rs w
    in either (const mempty) State.wcsHandlers (State.runResumable evts (unContract con))

record
    :: forall s e a.
       ( AllUniqueLabels (Output s)
       , Forall (Output s) Semigroup
       , Forall (Output s) Monoid
       )
    => Wallet
    -> ContractTraceResult s e a
    -> Either (ResumableError e) (Record (Event s))
record w rs =
    let (evts, con) = contractEventsWallet rs w
    in fmap State.wcsRecord (State.runResumable evts (unContract con))

not :: TracePredicate s e a -> TracePredicate s e a
not = PredF . fmap (fmap Prelude.not) . unPredF

checkPredicate
    :: forall s e a
    . ( Show e
      , AllUniqueLabels (Output s)
      , Forall (Input s) Pretty
      , Forall (Output s) Semigroup
      , Forall (Output s) Pretty
      , Forall (Output s) Monoid)
    => String
    -> Contract s e a
    -> TracePredicate s (TraceError e) a
    -> ContractTrace s e (EmulatorAction (TraceError e)) a ()
    -> TestTree
checkPredicate nm con predicate action =
    HUnit.testCaseSteps nm $ \step ->
        case runTrace con action of
            (Left err, _) ->
                HUnit.assertFailure $ "EmulatorAction failed. " ++ show err
            (Right (_, st), ms) -> do
                let dt = ContractTraceResult ms st
                    (result, testOutputs) = runWriter $ unPredF predicate (defaultDist, dt)
                unless result (step . Text.unpack $ renderTraceContext testOutputs st)
                HUnit.assertBool nm result

renderTraceContext
    :: forall s e a ann.
        ( Forall (Input s) Pretty
        , AllUniqueLabels (Output s)
        , Forall (Output s) Semigroup
        , Forall (Output s) Monoid
        , Forall (Output s) Pretty
        , Show e
        )
    => Doc ann
    -> ContractTraceState s e a
    -> Text.Text
renderTraceContext testOutputs st =
    let nonEmptyLogs =
            Map.toList
            $ Map.filter (P.not . null)
            $ eventsByWallet st
        theContract = unContract (view ctsContract st)
        results = fmap (\(wallet, events) -> (wallet, State.runResumable events theContract)) nonEmptyLogs
        prettyResults = fmap (\(wallet, res) -> hang 2 $ vsep ["Wallet:" <+> pretty wallet, prettyResult res]) results
        prettyResult result = case result of
            Left err ->
                hang 2 $ vsep ["Error:", viaShow err]
            Right (State.ResumableResult{State.wcsFinalState=Nothing, State.wcsHandlers}) ->
                hang 2 $ vsep ["Running, waiting for input:", pretty wcsHandlers]
            Right _ -> "Done"
    in renderStrict $ layoutPretty defaultLayoutOptions $ vsep
        [ hang 2 (vsep ["Test outputs:", testOutputs])
        , hang 2 (vsep ["Events by wallet:", prettyWalletEvents st])
        , hang 2 (vsep ["Contract result by wallet:", indent 2 $ vsep prettyResults])
        ]

prettyWalletEvents :: Forall (Input s) Pretty => ContractTraceState s e a -> Doc ann
prettyWalletEvents cts =
    let nonEmptyLogs =
            Map.toList
            $ Map.filter (P.not . null)
            $ eventsByWallet cts
        renderLog (wallet, events) =
            let events' = vsep $ fmap (\e -> "-" <+> nest 2 (pretty e)) $ toList events
            in nest 2 $ vsep ["Events for" <+> pretty wallet <> colon, events']
    in vsep (fmap renderLog nonEmptyLogs)

endpointAvailable
    :: forall (l :: Symbol) s e a.
       ( HasType l Endpoints.ActiveEndpoints (Output s)
       , KnownSymbol l
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Wallet
    -> TracePredicate s e a
endpointAvailable w = PredF $ \(_, r) ->
    if Endpoints.isActive @l @s (hooks w r)
    then pure True
    else do
        tell ("missing endpoint:" <+> fromString (symbolVal (Proxy :: Proxy l)))
        pure False

interestingAddress
    :: forall s e a.
       ( WatchAddress.HasWatchAddress s )
    => Wallet
    -> Address
    -> TracePredicate s e a
interestingAddress w addr = PredF $ \(_, r) -> do
    let hks = WatchAddress.addresses (hooks w r)
    if addr `Set.member` hks
    then pure True
    else do
        tell $ hsep
            [ "Interesting addresses of " <+> pretty w <> colon
                <+> nest 2 (concatWith (surround (comma <> space))  (viaShow <$> toList hks))
            , "Missing address:", viaShow addr
            ]
        pure False

tx
    :: forall s e a.
       ( HasType TxSymbol WriteTx.PendingTransactions (Output s)
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup)
    => Wallet
    -> (UnbalancedTx -> Bool)
    -> String
    -> TracePredicate s e a
tx w flt nm = PredF $ \(_, r) -> do
    let hks = WriteTx.transactions (hooks w r)
    if any flt hks
    then pure True
    else do
        tell $ hsep
            [ "Unbalanced transactions of" <+> pretty w <> colon
                <+> nest 2 (vsep (fmap pretty hks))
            , "No transaction with '" <> fromString nm <> "'"]
        pure False

walletState
    :: forall s e a.
       Wallet
    -> (EM.NodeClientState -> Bool)
    -> String
    -> TracePredicate s e a
walletState w flt nm = PredF $ \(_, r) -> do
    let ws = view (at w) $ EM._walletClientStates $  _ctrEmulatorState r
    case ws of
        Nothing -> do
            tell $ "Wallet state of " <+> pretty w <+> "not found"
            pure False
        Just st ->
            if flt st
            then pure True
            else do
                tell $ vsep
                    [ "Wallet state of '" <+> viaShow w <+> colon <+> viaShow st
                    , "Fails " <> squotes (fromString nm)
                    ]
                pure False

walletWatchingAddress
    :: forall s e a.
       Wallet
    -> Address
    -> TracePredicate s e a
walletWatchingAddress w addr =
    let desc = "watching address " <> show addr in
    walletState w (Map.member addr . AM.values . view EM.clientIndex) desc

assertEvents
    :: forall s e a.
       (Forall (Input s) Pretty)
    => Wallet
    -> ([Event s] -> Bool)
    -> String
    -> TracePredicate s e a
assertEvents w pr nm = PredF $ \(_, r) -> do
    let es = fmap (toList . walletEvents) (view (ctsWalletStates . at w) $ _ctrTraceState r)
    case es of
        Nothing -> do
            tell $ "Event log for" <+> pretty w <+> "not found"
            pure False
        Just lg ->
            if pr lg
            then pure True
            else do
                tell $ vsep
                    [ "Event log for" <+> pretty w <> ":"
                    , nest 2 (vsep (fmap pretty lg))
                    , "Fails" <+> squotes (fromString nm)
                    ]
                pure False

-- | Check that the funds at an address meet some condition.
fundsAtAddress
    :: forall s e a.
       Address
    -> (Value -> Bool)
    -> TracePredicate s e a
fundsAtAddress address check = PredF $ \(_, r) -> do
    let funds =
            Map.findWithDefault mempty address
            $ AM.values
            $ AM.fromChain
            $ view (EM.chainState . EM.chainNewestFirst)
            $ _ctrEmulatorState r
        passes = check funds
    unless passes
        $ tell ("Funds at address" <+> pretty address <+> "were" <> pretty funds)
    pure passes

waitingForSlot
    :: forall s e a.
       ( HasType SlotSymbol AwaitSlot.WaitingForSlot (Output s)
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Wallet
    -> Slot
    -> TracePredicate s e a
waitingForSlot w sl = PredF $ \(_, r) ->
    case AwaitSlot.nextSlot (hooks w r) of
        Nothing -> do
            tell $ pretty w <+> "not waiting for any slot notifications. Expected:" <+>  viaShow sl
            pure False
        Just sl' ->
            if sl == sl'
            then pure True
            else do
                tell $ pretty w <+> "waiting for" <+> viaShow sl' <+> "Expected:" <+> viaShow sl
                pure False

emulatorLog
    :: forall s e a.
       ()
    => ([EmulatorEvent] -> Bool)
    -> String
    -> TracePredicate s e a
emulatorLog f nm = PredF $ \(_, r) ->
    let lg = EM._emulatorLog $ _ctrEmulatorState r in
    if f lg
    then pure True
    else do
        tell $ vsep
            [ "Emulator log:"
            , nest 2 (vsep (fmap pretty lg))
            , "Fails" <+> squotes (fromString nm)
            ]
        pure False

anyTx
    :: forall s e a.
       ( HasType TxSymbol WriteTx.PendingTransactions (Output s)
       , AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       )
    => Wallet
    -> TracePredicate s e a
anyTx w = tx w (const True) "anyTx"

assertHooks
    :: forall s e a.
       ( AllUniqueLabels (Output s)
       , Forall (Output s) Monoid
       , Forall (Output s) Semigroup
       , Forall (Output s) Pretty
       )
    => Wallet
    -> (Handlers s -> Bool)
    -> String
    -> TracePredicate s e a
assertHooks w p nm = PredF $ \(_, rs) ->
    let hks = hooks w rs in
    if p hks
    then pure True
    else do
        tell $ vsep
            [ "Handlers for" <+> pretty w <> colon
            , nest 2 (pretty hks)
            , "Failed" <+> squotes (fromString nm)
            ]
        pure False

assertRecord
    :: forall s e a.
       ( Forall (Input s) Pretty
       , Forall (Output s) Semigroup
       , Forall (Output s) Monoid
       , AllUniqueLabels (Output s)
       , Show e
       )
    => Wallet
    -> (Record (Event s) -> Bool)
    -> String
    -> TracePredicate s e a
assertRecord w p nm = PredF $ \(_, rs) ->
    case record w rs of
        Right r
            | p r -> pure True
            | otherwise -> do
                tell $ vsep
                    [ "Record:"
                    , nest 2 (pretty r)
                    , "Failed" <+> squotes (fromString nm)
                    ]
                pure False
        Left err -> do
            tell $ pretty w <> colon <+> "Record failed with" <+> viaShow err <+> "in" <+> squotes (fromString nm)
            pure False

data Outcome e a =
    Done a
    -- ^ The contract finished without errors and produced a result
    | NotDone
    -- ^ The contract is waiting for more input.
    | Error (ResumableError e)
    -- ^ The contract failed with an error.
    deriving (Eq, Ord, Show)

-- | A 'TracePredicate' checking that the wallet's contract instance finished
--   without errors.
assertDone
    :: forall s e a.
    ( Forall (Input s) Pretty
    , AllUniqueLabels (Output s)
    , Forall (Output s) Semigroup
    , Forall (Output s) Monoid
    , Show e
    )
    => Wallet
    -> (a -> Bool)
    -> String
    -> TracePredicate s e a
assertDone w pr = assertOutcome w (\case { Done a -> pr a; _ -> False})

-- | A 'TracePredicate' checking that the wallet's contract instance is
--   waiting for input.
assertNotDone
    :: forall s e a.
    ( Forall (Input s) Pretty
    , AllUniqueLabels (Output s)
    , Forall (Output s) Semigroup
    , Forall (Output s) Monoid
    , Show e
    )
    => Wallet
    -> String
    -> TracePredicate s e a
assertNotDone w = assertOutcome w (\case { NotDone -> True; _ -> False})

-- | A 'TracePredicate' checking that the wallet's contract instance
--   failed with an error.
assertContractError
    :: forall s e a.
    ( Forall (Input s) Pretty
    , AllUniqueLabels (Output s)
    , Forall (Output s) Semigroup
    , Forall (Output s) Monoid
    , Show e
    )
    => Wallet
    -> (e -> Bool)
    -> String
    -> TracePredicate s e a
assertContractError w p =
    assertOutcome w (\case { Error (State.OtherError err) -> p err; _ -> False })

assertOutcome
    :: forall s e a.
       ( Forall (Input s) Pretty
       , AllUniqueLabels (Output s)
       , Forall (Output s) Semigroup
       , Forall (Output s) Monoid
       , Show e
       )
    => Wallet
    -> (Outcome e a -> Bool)
    -> String
    -> TracePredicate s e a
assertOutcome w p nm = PredF $ \(_, rs) ->
    let (evts, con) = contractEventsWallet rs w
        result = State.runResumable evts (unContract con)
    in
        case result of
            Left err
                | p (Error err) -> pure True
                | otherwise -> do
                    tell $ vsep
                        [ "Outcome of" <+> pretty w <> colon
                        , "Resumable error" <+> viaShow err
                        , "in" <+> squotes (fromString nm)
                        ]
                    pure False
            Right (State.ResumableResult{State.wcsRecord=Rec.OpenRec openRec})
                | p NotDone -> pure True
                | otherwise -> do
                    tell $ vsep
                        [ "Outcome of" <+> pretty w <> colon
                        , "Open record"
                        , pretty openRec
                        , "in" <+> squotes (fromString nm)
                        ]
                    pure False
            Right (State.ResumableResult{State.wcsRecord=Rec.ClosedRec closedRec, State.wcsFinalState=Just a})
                | p (Done a) -> pure True
                | otherwise -> do
                    tell $ vsep
                        [ "Outcome of" <+> pretty w <> colon
                        , "Closed record"
                        , pretty closedRec
                        , "failed with" <+> squotes (fromString nm)
                        ]
                    pure False
            _ -> pure False

contractEventsWallet
    :: ContractTraceResult s e a
    -> Wallet
    -> ([Event s], Contract s e a)
contractEventsWallet rs w =
    let evts = Map.findWithDefault [] w (eventsByWallet $ _ctrTraceState rs)
        con  = rs ^. ctrTraceState . ctsContract
    in (evts, con)

walletFundsChange
    :: forall s e a.
       ()
    => Wallet
    -> Value
    -> TracePredicate s e a
walletFundsChange w dlt = PredF $ \(initialDist, ContractTraceResult{_ctrEmulatorState = st}) ->
        let initialValue = fold (initialDist ^. at w)
            finalValue   = fromMaybe mempty (EM.fundsDistribution st ^. at w)
        in if initialValue P.+ dlt == finalValue
        then pure True
        else do
            tell $ vsep
                [ "Expected funds of" <+> pretty w <+> "to change by" <+> viaShow dlt
                , "but they changed by", viaShow (finalValue P.- initialValue)]
            pure False

-- | Assert that at least one transaction failed to validated, and that all
--   transactions that failed meet the predicate.
assertFailedTransaction
    :: forall s e a
    .  (TxId -> ValidationError -> Bool)
    -> TracePredicate s e a
assertFailedTransaction predicate = PredF $ \(_, ContractTraceResult{_ctrEmulatorState = st}) ->
    case failedTransactions (EM.emLog st) of
        [] -> do
            tell $ "No transactions failed to validate."
            pure False
        xs -> pure (all (uncurry predicate) xs)

-- | Assert that no transaction failed to validate.
assertNoFailedTransactions
    :: forall s e a.
    TracePredicate s e a
assertNoFailedTransactions = PredF $ \(_, ContractTraceResult{_ctrEmulatorState = st}) ->
    case failedTransactions (EM.emLog st) of
        [] -> pure True
        xs -> do
            tell $ vsep ("Transactions failed to validate:" : fmap pretty xs)
            pure False

failedTransactions :: [EM.EmulatorEvent] -> [(TxId, ValidationError)]
failedTransactions = mapMaybe $
    \case
        EM.ChainEvent (EM.TxnValidationFail txid err) -> Just (txid, err)
        _ -> Nothing
