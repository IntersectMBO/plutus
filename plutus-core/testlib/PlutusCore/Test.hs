{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE UndecidableInstances   #-}

module PlutusCore.Test (
  checkFails,
  ToTPlc (..),
  ToUPlc (..),
  pureTry,
  catchAll,
  rethrow,
  runTPlc,
  runUPlc,
  ppThrow,
  ppCatch,
  goldenTPlcWith,
  goldenTPlc,
  goldenTPlcCatch,
  goldenUPlcWith,
  goldenUPlc,
  goldenUPlcCatch,
  goldenUPlcReadable,
  goldenTEval,
  goldenUEval,
  goldenTEvalCatch,
  goldenUEvalCatch,
  goldenUEvalProfile,
  goldenUPlcBudget,
  initialSrcSpan,
  topSrcSpan,
  NoMarkRenameT (..),
  noMarkRename,
  NoRenameT (..),
  noRename,
  BrokenRenameT (..),
  runBrokenRenameT,
  runUPlcProfile,
  runUPlcProfileExec,
  brokenRename,
  Prerename (..),
  BindingRemoval (..),
  prop_scopingFor,
  test_scopingGood,
  test_scopingBad,
  test_scopingSpoilRenamer,
  -- * Tasty extras
  module TastyExtras,
) where

import Test.Tasty.Extras as TastyExtras

import PlutusPrelude

import PlutusCore.Generators.Hedgehog.AST
import PlutusCore.Generators.Hedgehog.Utils

import PlutusCore qualified as TPLC
import PlutusCore.Annotation
import PlutusCore.Check.Scoping
import PlutusCore.DeBruijn
import PlutusCore.Evaluation.Machine.Ck qualified as TPLC
import PlutusCore.Evaluation.Machine.ExBudget qualified as TPLC
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as TPLC
import PlutusCore.Pretty
import PlutusCore.Rename.Monad qualified as TPLC

import Control.Exception
import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Either.Extras
import Data.Text (Text)
import Hedgehog
import Prettyprinter qualified as PP
import System.IO.Unsafe
import Test.Tasty hiding (after)
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

import Hedgehog.Internal.Config
import Hedgehog.Internal.Property
import Hedgehog.Internal.Region
import Hedgehog.Internal.Report
import Hedgehog.Internal.Runner

-- | Map the 'TestLimit' of a 'Property' with a given function.
mapTestLimit :: (TestLimit -> TestLimit) -> Property -> Property
mapTestLimit f =
  mapConfig $ \config ->
    config
      { propertyTerminationCriteria = case propertyTerminationCriteria config of
          NoEarlyTermination c tests    -> NoEarlyTermination c $ f tests
          NoConfidenceTermination tests -> NoConfidenceTermination $ f tests
          EarlyTermination c tests      -> EarlyTermination c $ f tests
      }

{- | Set the number of times a property should be executed before it is considered
successful, unless it's already higher than that.
-}
withAtLeastTests :: TestLimit -> Property -> Property
withAtLeastTests = mapTestLimit . max

{- | @check@ is supposed to just check if the property fails or not, but for some stupid reason it
also performs shrinking and prints the counterexample and other junk. This function is like
@check@, but doesn't do any of that.
-}
checkQuiet :: (MonadIO m) => Property -> m Bool
checkQuiet prop = do
  color <- detectColor
  -- This is what causes @hedgehog@ to shut up.
  region <- liftIO newEmptyRegion
  -- For some reason @hedgehog@ thinks it's a good idea to shrink a counterexample in case of
  -- an expected failure, so we suppress that.
  let propNoShrink = withShrinks 0 prop
  liftIO $ (== OK) . reportStatus <$> checkNamed region color Nothing Nothing propNoShrink

-- | Check that the given 'Property' fails.
checkFails :: Property -> IO ()
-- 'withAtLeastTests' gives the property that is supposed to fail some room in order for it to
-- reach a failing test case.
checkFails = checkQuiet . withAtLeastTests 1000 >=> \res -> res @?= False

{- | Class for ad-hoc overloading of things which can be turned into a PLC program. Any errors
from the process should be caught.
-}
class ToTPlc a uni fun | a -> uni fun where
  toTPlc :: a -> ExceptT SomeException IO (TPLC.Program TPLC.TyName TPLC.Name uni fun ())

instance (ToTPlc a uni fun) => ToTPlc (ExceptT SomeException IO a) uni fun where
  toTPlc a = a >>= toTPlc

instance ToTPlc (TPLC.Program TPLC.TyName TPLC.Name uni fun ()) uni fun where
  toTPlc = pure

class ToUPlc a uni fun | a -> uni fun where
  toUPlc :: a -> ExceptT SomeException IO (UPLC.Program TPLC.Name uni fun ())

instance (ToUPlc a uni fun) => ToUPlc (ExceptT SomeException IO a) uni fun where
  toUPlc a = a >>= toUPlc

instance ToUPlc (UPLC.Program TPLC.Name uni fun ()) uni fun where
  toUPlc = pure

instance ToUPlc (UPLC.Program UPLC.NamedDeBruijn uni fun ()) uni fun where
  toUPlc p =
    withExceptT @_ @FreeVariableError toException $
      TPLC.runQuoteT $
        traverseOf
          UPLC.progTerm
          UPLC.unDeBruijnTerm
          p

pureTry :: (Exception e) => a -> Either e a
pureTry = unsafePerformIO . try . evaluate

catchAll :: a -> ExceptT SomeException IO a
catchAll value = ExceptT $ try @SomeException (evaluate value)

rethrow :: ExceptT SomeException IO a -> IO a
rethrow = fmap unsafeFromEither . runExceptT

runTPlc ::
  (ToTPlc a TPLC.DefaultUni TPLC.DefaultFun) =>
  [a] ->
  ExceptT
    SomeException
    IO
    (TPLC.EvaluationResult (TPLC.Term TPLC.TyName TPLC.Name TPLC.DefaultUni TPLC.DefaultFun ()))
runTPlc values = do
  ps <- traverse toTPlc values
  let (TPLC.Program _ _ t) =
        foldl1
          (unsafeFromRight .* TPLC.applyProgram)
          ps
  liftEither . first toException . TPLC.extractEvaluationResult $
    TPLC.evaluateCkNoEmit TPLC.defaultBuiltinsRuntime t

runUPlc ::
  (ToUPlc a TPLC.DefaultUni TPLC.DefaultFun) =>
  [a] ->
  ExceptT
    SomeException
    IO
    (UPLC.EvaluationResult (UPLC.Term TPLC.Name TPLC.DefaultUni TPLC.DefaultFun ()))
runUPlc values = do
  ps <- traverse toUPlc values
  let (UPLC.Program _ _ t) = foldl1 (unsafeFromRight .* UPLC.applyProgram) ps
  liftEither . first toException . TPLC.extractEvaluationResult $
    UPLC.evaluateCekNoEmit TPLC.defaultCekParameters t

runUPlcBudget ::
  (ToUPlc a TPLC.DefaultUni UPLC.DefaultFun) =>
  [a] ->
  ExceptT
    SomeException
    IO
    (UPLC.Term UPLC.Name TPLC.DefaultUni UPLC.DefaultFun (), TPLC.ExBudget)
runUPlcBudget values = do
  ps <- traverse toUPlc values
  let (UPLC.Program _ _ t) = foldl1 (unsafeFromRight .* UPLC.applyProgram) ps
  let (result, UPLC.CountingSt budget) =
        UPLC.runCekNoEmit TPLC.defaultCekParameters UPLC.counting t
  res <- fromRightM (throwError . SomeException) result
  pure (res, budget)

-- For golden tests of profiling.
runUPlcProfile ::
  (ToUPlc a TPLC.DefaultUni UPLC.DefaultFun) =>
  [a] ->
  ExceptT
    SomeException
    IO
    (UPLC.Term UPLC.Name TPLC.DefaultUni UPLC.DefaultFun (), [Text])
runUPlcProfile values = do
  ps <- traverse toUPlc values
  let (UPLC.Program _ _ t) = foldl1 (unsafeFromRight .* UPLC.applyProgram) ps
      (result, logOut) = UPLC.evaluateCek UPLC.logEmitter TPLC.defaultCekParameters t
  res <- fromRightM (throwError . SomeException) result
  pure (res, logOut)

-- For the profiling executable.
runUPlcProfileExec ::
  (ToUPlc a TPLC.DefaultUni UPLC.DefaultFun) =>
  [a] ->
  ExceptT
    SomeException
    IO
    (UPLC.Term UPLC.Name TPLC.DefaultUni UPLC.DefaultFun (), [Text])
runUPlcProfileExec values = do
  ps <- traverse toUPlc values
  let (UPLC.Program _ _ t) = foldl1 (unsafeFromRight .* UPLC.applyProgram) ps
      (result, logOut) = UPLC.evaluateCek UPLC.logWithTimeEmitter TPLC.defaultCekParameters t
  res <- fromRightM (throwError . SomeException) result
  pure (res, logOut)

ppCatch :: (PrettyPlc a) => ExceptT SomeException IO a -> IO (Doc ann)
ppCatch value = either (PP.pretty . show) prettyPlcClassicDebug <$> runExceptT value

ppThrow :: (PrettyPlc a) => ExceptT SomeException IO a -> IO (Doc ann)
ppThrow value = rethrow $ prettyPlcClassicDebug <$> value

ppThrowReadable ::
  (PrettyBy (PrettyConfigReadable PrettyConfigName) a) =>
  ExceptT SomeException IO a ->
  IO (Doc ann)
ppThrowReadable value = rethrow $ pretty . AsReadable <$> value

goldenTPlcWith ::
  (ToTPlc a TPLC.DefaultUni TPLC.DefaultFun) =>
  String ->
  ( ExceptT
      SomeException
      IO
      (TPLC.Program TPLC.NamedTyDeBruijn TPLC.NamedDeBruijn TPLC.DefaultUni TPLC.DefaultFun ()) ->
    IO (Doc ann)
  ) ->
  String ->
  a ->
  TestNested
goldenTPlcWith ext pp name value = nestedGoldenVsDocM name ext $ pp $ do
  p <- toTPlc value
  withExceptT @_ @FreeVariableError toException $ traverseOf TPLC.progTerm deBruijnTerm p

goldenTPlc ::
  (ToTPlc a TPLC.DefaultUni TPLC.DefaultFun) =>
  String ->
  a ->
  TestNested
goldenTPlc = goldenTPlcWith ".tplc" ppThrow

goldenTPlcCatch ::
  (ToTPlc a TPLC.DefaultUni TPLC.DefaultFun) =>
  String ->
  a ->
  TestNested
goldenTPlcCatch = goldenTPlcWith ".tplc-catch" ppCatch

goldenUPlcWith ::
  (ToUPlc a UPLC.DefaultUni UPLC.DefaultFun) =>
  String ->
  ( ExceptT
      SomeException
      IO
      (UPLC.Program UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()) ->
    IO (Doc ann)
  ) ->
  String ->
  a ->
  TestNested
goldenUPlcWith ext pp name value = nestedGoldenVsDocM name ext $ pp $ do
  p <- toUPlc value
  withExceptT @_ @FreeVariableError toException $ traverseOf UPLC.progTerm UPLC.deBruijnTerm p

goldenUPlc ::
  (ToUPlc a UPLC.DefaultUni UPLC.DefaultFun) =>
  String ->
  a ->
  TestNested
goldenUPlc = goldenUPlcWith ".uplc" ppThrow

goldenUPlcReadable ::
  (ToUPlc a UPLC.DefaultUni UPLC.DefaultFun) =>
  String ->
  a ->
  TestNested
goldenUPlcReadable = goldenUPlcWith ".uplc-readable" ppThrowReadable

goldenUPlcCatch ::
  (ToUPlc a UPLC.DefaultUni UPLC.DefaultFun) =>
  String ->
  a ->
  TestNested
goldenUPlcCatch = goldenUPlcWith ".uplc-catch" ppCatch

goldenTEval ::
  (ToTPlc a TPLC.DefaultUni TPLC.DefaultFun) =>
  String ->
  [a] ->
  TestNested
goldenTEval name values =
  nestedGoldenVsDocM name ".teval" $ prettyPlcClassicDebug <$> (rethrow $ runTPlc values)

goldenUEval ::
  (ToUPlc a TPLC.DefaultUni TPLC.DefaultFun) =>
  String ->
  [a] ->
  TestNested
goldenUEval name values =
  nestedGoldenVsDocM name ".ueval" $ prettyPlcClassicDebug <$> (rethrow $ runUPlc values)

goldenTEvalCatch ::
  (ToTPlc a TPLC.DefaultUni TPLC.DefaultFun) =>
  String ->
  [a] ->
  TestNested
goldenTEvalCatch name values = nestedGoldenVsDocM name ".teval-catch" $ ppCatch $ runTPlc values

goldenUEvalCatch ::
  (ToUPlc a TPLC.DefaultUni TPLC.DefaultFun) =>
  String ->
  [a] ->
  TestNested
goldenUEvalCatch name values = nestedGoldenVsDocM name ".ueval-catch" $ ppCatch $ runUPlc values

-- | Similar to @goldenUEval@ but with profiling turned on.
goldenUEvalProfile ::
  (ToUPlc a TPLC.DefaultUni TPLC.DefaultFun) =>
  String ->
  [a] ->
  TestNested
goldenUEvalProfile name values =
  nestedGoldenVsDocM name ".ueval-profile" $
    pretty . view _2 <$> (rethrow $ runUPlcProfile values)

goldenUPlcBudget ::
  (ToUPlc a TPLC.DefaultUni TPLC.DefaultFun)
  => String
  -> [a]
  -> TestNested
goldenUPlcBudget name values =
  nestedGoldenVsDocM name ".budget" $ ppCatch $ view _2 <$> runUPlcBudget values

-- | A made-up `SrcSpan` for testing.
initialSrcSpan :: FilePath -> SrcSpan
initialSrcSpan fp = SrcSpan fp 1 1 1 2

topSrcSpan :: SrcSpan
topSrcSpan = initialSrcSpan "top"

-- See Note [Marking].

-- | A version of 'RenameT' that fails to take free variables into account.
newtype NoMarkRenameT ren m a = NoMarkRenameT
  { unNoMarkRenameT :: TPLC.RenameT ren m a
  }
  deriving newtype
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadReader ren
    , TPLC.MonadQuote
    )

noMarkRename ::
  (Monoid ren) =>
  (t -> NoMarkRenameT ren m t) ->
  t ->
  m t
noMarkRename renM = TPLC.runRenameT . unNoMarkRenameT . renM

-- | A version of 'RenameT' that does not perform any renaming at all.
newtype NoRenameT ren m a = NoRenameT
  { unNoRenameT :: m a
  }
  deriving newtype
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , TPLC.MonadQuote
    )

instance (Monad m, Monoid ren) => MonadReader ren (NoRenameT ren m) where
  ask = pure mempty
  local _ = id

noRename ::
  (TPLC.MonadQuote m) =>
  (t -> m ()) ->
  (t -> NoRenameT ren m t) ->
  t ->
  m t
noRename mark renM = through mark >=> unNoRenameT . renM

{- | A broken version of 'RenameT' whose 'local' updates the scope globally
(as opposed to locally).
-}
newtype BrokenRenameT ren m a = BrokenRenameT
  { unBrokenRenameT :: StateT ren m a
  }
  deriving newtype
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadState ren
    , TPLC.MonadQuote
    )

instance (Monad m) => MonadReader ren (BrokenRenameT ren m) where
  ask = get
  local f a = modify f *> a

runBrokenRenameT :: (Monad m, Monoid ren) => BrokenRenameT ren m a -> m a
runBrokenRenameT = flip evalStateT mempty . unBrokenRenameT

brokenRename ::
  (TPLC.MonadQuote m, Monoid ren) =>
  (t -> m ()) ->
  (t -> BrokenRenameT ren m t) ->
  t ->
  m t
brokenRename mark renM = through mark >=> runBrokenRenameT . renM

{- Note [Scoping tests API]
If you want to test how a certain pass handles scoping you should use either 'test_scopingGood' or
'test_scopingBad' depending on whether the pass is expected to preserve global uniqueness and not
change scoping of its argument. Regarding the last one: substitution, for example, may remove free
variables and scoping tests, being initially developed only to test renamers, will fail upon seeing
that a free variable was removed. So any scoping test failure needs to be carefully scrutinized
before concluding that it reveals a bug.

As it turns out, most AST transformations don't do anything that would cause the scoping tests to
false-positively report a bug:

- a lot of passes simply do not do anything with names apart from maybe moving them around
- those that do change names may produce alpha-equivalent results and this is one thing that the
  scoping machinery is designed to test
- some passes such as inlining may duplicate binders, but that is also fine as long as the
  duplicates are properly renamed, since the scoping machinery doesn't count binders or variable
  usages, it only expects free names to stay free, bound names to change together with their binders
  and global uniqueness to be preserved (see 'ScopeError' for the full list of possible errors)
- some passes such as inlining may remove bindings and there's special support implemented for
  handling this: when invoking either 'test_scopingGood' or 'test_scopingBad' you need to provide a
  'BindingRemoval' argument specifying whether binding removal is expected for the pass. Conversily,
  make it 'BindingRemovalOk' whenever you use 'test_scopingBad' to emphasize that even with binding
  removal allowed tests still fail
- some passes do not perform renaming of the input themselves, in that case you need to provide
  'PrerenameYes' for the 'Prerename' argument that both the test runners expect. It doesn't matter
  whether the pass relies on global uniqueness itself, because the scoping tests rely on it anyway.
  If the pass renames its input, and only in this case, provide 'PrerenameNo' for the 'Prerename'
  argument, this will allow the scoping tests to ensure that the pass does indeed rename its input
- due to a very specific design of the scoping tests some passes don't give false positives, but
  don't get tested properly either. For example dead code elimination is a no-op within the scoping
  tests, because internally all types/terms/programs only contain bindings that get referenced

There's also 'test_scopingSpoilRenamer', this one is used to test that the scoping tests do catch
various kinds of bugs. Don't use it with any passes that aren't renamers.

All in all, in order to use the scoping tests you have to understand how they work, which is an
unfortunate but seemingly inevitable requirement. On the bright side, it's worth the effort, because
the tests do catch bugs occasionally.

Whenever you use 'test_scopingBad' make sure to explain why, so that it's clear whether there's
something wrong with the pass or it's just a limitation of the scoping tests.
-}

-- | Determines whether to perform renaming before running the scoping tests. Needed for passes that
-- don't perform renaming themselves.
data Prerename =
  PrerenameYes |
  PrerenameNo

runPrerename :: TPLC.Rename a => Prerename -> a -> a
runPrerename PrerenameYes = TPLC.runQuote . TPLC.rename
runPrerename PrerenameNo  = id

-- | Test scoping for a renamer.
prop_scopingFor ::
  (PrettyPlc (t NameAnn), TPLC.Rename (t NameAnn), Scoping t) =>
  -- | A generator of types\/terms\/programs.
  AstGen (t ann) ->
  -- | Whether binding removal is expected for the pass.
  BindingRemoval ->
  -- | Whether renaming is required before running the scoping tests. Note that the scoping tests
  -- rely on global uniqueness themselves, hence for any pass that doesn't perform renaming
  -- internally this needs to be 'PrerenameYes'.
  Prerename ->
  -- | The runner of the pass.
  (t NameAnn -> TPLC.Quote (t NameAnn)) ->
  Property
prop_scopingFor gen bindRem preren run = withTests 1000 . property $ do
  prog <- forAllNoShow $ runAstGen gen
  let catchEverything = unsafePerformIO . try @SomeException . evaluate
      prep = runPrerename preren
  case catchEverything $ checkRespectsScoping bindRem prep (TPLC.runQuote . run) prog of
    Left exc         -> fail $ displayException exc
    Right (Left err) -> fail $ displayPlcDef err
    Right (Right ()) -> success

-- | Test that a pass does not break global uniqueness.
test_scopingGood ::
  (PrettyPlc (t NameAnn), TPLC.Rename (t NameAnn), Scoping t) =>
  -- | The name of the pass we're about to test.
  String ->
  -- | A generator of types\/terms\/programs.
  AstGen (t ann) ->
  -- | Whether binding removal is expected for the pass.
  BindingRemoval ->
  -- | Whether renaming is required before running the scoping tests. Note that the scoping tests
  -- rely on global uniqueness themselves, hence for any pass that doesn't perform renaming
  -- internally this needs to be 'PrerenameYes'.
  Prerename ->
  -- | The runner of the pass.
  (t NameAnn -> TPLC.Quote (t NameAnn)) ->
  TestTree
test_scopingGood pass gen bindRem preren run =
  testPropertyNamed (pass ++ " does not break scoping and global uniqueness") "test_scopingGood" $
    prop_scopingFor gen bindRem preren run

-- | Test that a pass breaks global uniqueness.
test_scopingBad ::
  (PrettyPlc (t NameAnn), TPLC.Rename (t NameAnn), Scoping t) =>
  -- | The name of the pass we're about to test.
  String ->
  -- | A generator of types\/terms\/programs.
  AstGen (t ann) ->
  -- | Whether binding removal is expected for the pass.
  BindingRemoval ->
  -- | Whether renaming is required before running the scoping tests. Note that the scoping tests
  -- rely on global uniqueness themselves, hence for any pass that doesn't perform renaming
  -- internally this needs to be 'PrerenameYes'.
  Prerename ->
  -- | The runner of the pass.
  (t NameAnn -> TPLC.Quote (t NameAnn)) ->
  TestTree
test_scopingBad pass gen bindRem preren run =
  testCase (pass ++ " breaks scoping or global uniqueness") . checkFails $
    prop_scopingFor gen bindRem preren run

-- | Test that the scoping machinery fails when the given renamer is spoiled in some way
-- (e.g. marking is removed) to ensure that the machinery does catch bugs.
test_scopingSpoilRenamer ::
  (PrettyPlc (t NameAnn), TPLC.Rename (t NameAnn), Scoping t, Monoid ren) =>
  AstGen (t ann) ->
  (t NameAnn -> TPLC.Quote ()) ->
  (forall m. (TPLC.MonadQuote m, MonadReader ren m) => t NameAnn -> m (t NameAnn)) ->
  TestTree
test_scopingSpoilRenamer gen mark renM =
  testGroup
    "bad renaming"
    [ test_scopingBad "wrong renaming" gen BindingRemovalNotOk PrerenameNo $
        brokenRename mark renM
    , test_scopingBad "no renaming" gen BindingRemovalNotOk PrerenameNo $
        noRename mark renM
    , test_scopingBad "renaming with no marking" gen BindingRemovalNotOk PrerenameNo $
        noMarkRename renM
    ]
