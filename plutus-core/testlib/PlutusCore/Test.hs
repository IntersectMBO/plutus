{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE UndecidableInstances   #-}

module PlutusCore.Test
    ( checkFails
    , ToTPlc(..)
    , ToUPlc(..)
    , pureTry
    , catchAll
    , rethrow
    , runTPlc
    , runUPlc
    , goldenTPlc
    , goldenTPlcCatch
    , goldenUPlc
    , goldenUPlcCatch
    , goldenTEval
    , goldenUEval
    , goldenTEvalCatch
    , goldenUEvalCatch
    , goldenUEvalProfile
    , NoMarkRenameT(..)
    , noMarkRename
    , NoRenameT(..)
    , noRename
    , BrokenRenameT(..)
    , runBrokenRenameT
    , runUPlcProfile
    , runUPlcProfileExec
    , brokenRename
    , prop_scopingFor
    , test_scopingGood
    , test_scopingBad
    -- * Tasty extras
    , module TastyExtras
    ) where

import PlutusPrelude

import Test.Tasty.Extras as TastyExtras

import PlutusCore qualified as TPLC
import PlutusCore.Check.Scoping
import PlutusCore.DeBruijn
import PlutusCore.Evaluation.Machine.Ck qualified as TPLC
import PlutusCore.Generators
import PlutusCore.Generators.AST
import PlutusCore.Pretty
import PlutusCore.Rename.Monad qualified as TPLC

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

import Control.Exception
import Control.Lens
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Text (Text)
import Hedgehog
import Prettyprinter qualified as PP
import System.IO.Unsafe
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog

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

-- | Set the number of times a property should be executed before it is considered
-- successful, unless it's already higher than that.
withAtLeastTests :: TestLimit -> Property -> Property
withAtLeastTests = mapTestLimit . max

-- | @check@ is supposed to just check if the property fails or not, but for some stupid reason it
-- also performs shrinking and prints the counterexample and other junk. This function is like
-- @check@, but doesn't do any of that.
checkQuiet :: MonadIO m => Property -> m Bool
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

-- | Class for ad-hoc overloading of things which can be turned into a PLC program. Any errors
-- from the process should be caught.
class ToTPlc a uni fun | a -> uni fun where
    toTPlc :: a -> ExceptT SomeException IO (TPLC.Program TPLC.TyName TPLC.Name uni fun ())

instance ToTPlc a uni fun => ToTPlc (ExceptT SomeException IO a) uni fun where
    toTPlc a = a >>= toTPlc

instance ToTPlc (TPLC.Program TPLC.TyName TPLC.Name uni fun ()) uni fun where
    toTPlc = pure

class ToUPlc a uni fun | a -> uni fun where
    toUPlc :: a -> ExceptT SomeException IO (UPLC.Program TPLC.Name uni fun ())

instance ToUPlc a uni fun => ToUPlc (ExceptT SomeException IO a) uni fun where
    toUPlc a = a >>= toUPlc

instance ToUPlc (UPLC.Program TPLC.Name uni fun ()) uni fun where
    toUPlc = pure

instance ToUPlc (UPLC.Program UPLC.NamedDeBruijn uni fun ()) uni fun where
    toUPlc p = withExceptT @_ @FreeVariableError toException $ TPLC.runQuoteT $ traverseOf UPLC.progTerm UPLC.unDeBruijnTerm p

pureTry :: Exception e => a -> Either e a
pureTry = unsafePerformIO . try . evaluate

catchAll :: a -> ExceptT SomeException IO a
catchAll value = ExceptT $ try @SomeException (evaluate value)

rethrow :: ExceptT SomeException IO a -> IO a
rethrow = fmap (either throw id) . runExceptT

runTPlc
    :: ToTPlc a TPLC.DefaultUni TPLC.DefaultFun
    => [a]
    -> ExceptT SomeException IO (TPLC.EvaluationResult (TPLC.Term TPLC.TyName TPLC.Name TPLC.DefaultUni TPLC.DefaultFun ()))
runTPlc values = do
    ps <- traverse toTPlc values
    let (TPLC.Program _ _ t) = foldl1 TPLC.applyProgram ps
    liftEither $ first toException $ TPLC.extractEvaluationResult $ TPLC.evaluateCkNoEmit TPLC.defaultBuiltinsRuntime t

runUPlc
    :: ToUPlc a TPLC.DefaultUni TPLC.DefaultFun
    => [a]
    -> ExceptT SomeException IO (UPLC.EvaluationResult (UPLC.Term TPLC.Name TPLC.DefaultUni TPLC.DefaultFun ()))
runUPlc values = do
    ps <- traverse toUPlc values
    let (UPLC.Program _ _ t) = foldl1 UPLC.applyProgram ps
    liftEither $ first toException $ TPLC.extractEvaluationResult $ UPLC.evaluateCekNoEmit TPLC.defaultCekParameters t

-- For golden tests of profiling.
runUPlcProfile :: ToUPlc a TPLC.DefaultUni UPLC.DefaultFun =>
    [a]
    -> ExceptT
     SomeException
     IO
     (UPLC.Term UPLC.Name TPLC.DefaultUni UPLC.DefaultFun (), [Text])
runUPlcProfile values = do
    ps <- traverse toUPlc values
    let (UPLC.Program _ _ t) = foldl1 UPLC.applyProgram ps
        (result, logOut) = UPLC.evaluateCek UPLC.logEmitter TPLC.defaultCekParameters t
    res <- either (throwError . SomeException) pure result
    pure (res, logOut)

-- For the profiling executable.
runUPlcProfileExec :: ToUPlc a TPLC.DefaultUni UPLC.DefaultFun =>
    [a]
    -> ExceptT
     SomeException
     IO
     (UPLC.Term UPLC.Name TPLC.DefaultUni UPLC.DefaultFun (), [Text])
runUPlcProfileExec values = do
    ps <- traverse toUPlc values
    let (UPLC.Program _ _ t) = foldl1 UPLC.applyProgram ps
        (result, logOut) = UPLC.evaluateCek UPLC.logWithTimeEmitter TPLC.defaultCekParameters t
    res <- either (throwError . SomeException) pure result
    pure (res, logOut)

ppCatch :: PrettyPlc a => ExceptT SomeException IO a -> IO (Doc ann)
ppCatch value = either (PP.pretty . show) prettyPlcClassicDebug <$> runExceptT value

ppThrow :: PrettyPlc a => ExceptT SomeException IO a -> IO (Doc ann)
ppThrow value = rethrow $ prettyPlcClassicDebug <$> value

goldenTPlc
    :: ToTPlc a TPLC.DefaultUni TPLC.DefaultFun
    => String -> a -> TestNested
goldenTPlc name value = nestedGoldenVsDocM name $ ppThrow $ do
    p <- toTPlc value
    withExceptT @_ @FreeVariableError toException $ traverseOf TPLC.progTerm deBruijnTerm p

goldenTPlcCatch
    :: ToTPlc a TPLC.DefaultUni TPLC.DefaultFun
    => String -> a -> TestNested
goldenTPlcCatch name value = nestedGoldenVsDocM name $ ppCatch $ do
    p <- toTPlc value
    withExceptT @_ @FreeVariableError toException $ traverseOf TPLC.progTerm deBruijnTerm p

goldenUPlc
    :: ToUPlc a TPLC.DefaultUni TPLC.DefaultFun
     => String -> a -> TestNested
goldenUPlc name value = nestedGoldenVsDocM name $ ppThrow $ do
    p <- toUPlc value
    withExceptT @_ @FreeVariableError toException $ traverseOf UPLC.progTerm UPLC.deBruijnTerm p

goldenUPlcCatch
    :: ToUPlc a TPLC.DefaultUni TPLC.DefaultFun
    => String -> a -> TestNested
goldenUPlcCatch name value = nestedGoldenVsDocM name $ ppCatch $ do
    p <- toUPlc value
    withExceptT @_ @FreeVariableError toException $ traverseOf UPLC.progTerm UPLC.deBruijnTerm p

goldenTEval
    :: ToTPlc a TPLC.DefaultUni TPLC.DefaultFun
    => String -> [a] -> TestNested
goldenTEval name values = nestedGoldenVsDocM name $ prettyPlcClassicDebug <$> (rethrow $ runTPlc values)

goldenUEval
    :: ToUPlc a TPLC.DefaultUni TPLC.DefaultFun
    => String -> [a] -> TestNested
goldenUEval name values = nestedGoldenVsDocM name $ prettyPlcClassicDebug <$> (rethrow $ runUPlc values)

goldenTEvalCatch
    :: ToTPlc a TPLC.DefaultUni TPLC.DefaultFun
    => String -> [a] -> TestNested
goldenTEvalCatch name values = nestedGoldenVsDocM name $ ppCatch $ runTPlc values

goldenUEvalCatch
    :: ToUPlc a TPLC.DefaultUni TPLC.DefaultFun
    => String -> [a] -> TestNested
goldenUEvalCatch name values = nestedGoldenVsDocM name $ ppCatch $ runUPlc values

-- | Similar to @goldenUEval@ but with profiling turned on.
goldenUEvalProfile
    :: ToUPlc a TPLC.DefaultUni TPLC.DefaultFun
    => String -> [a] -> TestNested
goldenUEvalProfile name values = nestedGoldenVsDocM name $ pretty . view _2 <$> (rethrow $ runUPlcProfile values)

-- See Note [Marking].
-- | A version of 'RenameT' that fails to take free variables into account.
newtype NoMarkRenameT ren m a = NoMarkRenameT
    { unNoMarkRenameT :: TPLC.RenameT ren m a
    } deriving newtype
        ( Functor, Applicative, Alternative, Monad
        , MonadReader ren
        , TPLC.MonadQuote
        )

noMarkRename
    :: Monoid ren
    => (t -> NoMarkRenameT ren m t)
    -> t
    -> m t
noMarkRename renM = TPLC.runRenameT . unNoMarkRenameT . renM

-- | A version of 'RenameT' that does not perform any renaming at all.
newtype NoRenameT ren m a = NoRenameT
    { unNoRenameT :: m a
    } deriving newtype
        ( Functor, Applicative, Alternative, Monad
        , TPLC.MonadQuote
        )

instance (Monad m, Monoid ren) => MonadReader ren (NoRenameT ren m) where
    ask = pure mempty
    local _ = id

noRename
    :: TPLC.MonadQuote m
    => (t -> m ())
    -> (t -> NoRenameT ren m t)
    -> t
    -> m t
noRename mark renM = through mark >=> unNoRenameT . renM

-- | A broken version of 'RenameT' whose 'local' updates the scope globally (as opposed to locally).
newtype BrokenRenameT ren m a = BrokenRenameT
    { unBrokenRenameT :: StateT ren m a
    } deriving newtype
        ( Functor, Applicative, Alternative, Monad
        , MonadState ren
        , TPLC.MonadQuote
        )

instance Monad m => MonadReader ren (BrokenRenameT ren m) where
    ask = get
    local f a = modify f *> a

runBrokenRenameT :: (Monad m, Monoid ren) => BrokenRenameT ren m a -> m a
runBrokenRenameT = flip evalStateT mempty . unBrokenRenameT

brokenRename
    :: (TPLC.MonadQuote m, Monoid ren)
    => (t -> m ())
    -> (t -> BrokenRenameT ren m t)
    -> t
    -> m t
brokenRename mark renM = through mark >=> runBrokenRenameT . renM

-- | Test scoping for a renamer.
prop_scopingFor
    :: (Pretty (t ann), Scoping t)
    => AstGen (t ann) -> (t NameAnn -> TPLC.Quote (t NameAnn)) -> Property
prop_scopingFor gen ren = property $ do
    prog <- forAllPretty $ runAstGen gen
    let catchEverything = unsafePerformIO . try @SomeException . evaluate
    case catchEverything $ checkRespectsScoping (TPLC.runQuote . ren) prog of
        Left  exc        -> fail $ show exc
        Right (Left err) -> fail $ show err
        Right (Right ()) -> success

-- | Test that a good renamer does not destroy scoping.
test_scopingGood
    :: (Pretty (t ann), Scoping t)
    => AstGen (t ann)
    -> (t NameAnn -> TPLC.Quote (t NameAnn))
    -> TestTree
test_scopingGood gen ren =
    testProperty "renamer does not destroy scoping" $
        prop_scopingFor gen ren

-- | Test that a renaming machinery destroys scoping when a bad renamer is chosen.
test_scopingBad
    :: (Pretty (t ann), Scoping t, Monoid ren)
    => AstGen (t ann)
    -> (t NameAnn -> TPLC.Quote ())
    -> (forall m. (TPLC.MonadQuote m, MonadReader ren m) => t NameAnn -> m (t NameAnn))
    -> TestTree
test_scopingBad gen mark renM =
    testGroup "scoping bad"
        [ testCase "wrong renaming destroys scoping" $
            checkFails . prop_scopingFor gen $ brokenRename mark renM
        , testCase "no renaming does not result in global uniqueness" $
            checkFails . prop_scopingFor gen $ noRename mark renM
        , testCase "renaming with no marking destroys scoping" $
            checkFails . prop_scopingFor gen $ noMarkRename renM
        ]
