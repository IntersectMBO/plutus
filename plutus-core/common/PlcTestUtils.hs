{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module PlcTestUtils (
    ToTPlc(..),
    ToUPlc(..),
    pureTry,
    catchAll,
    rethrow,
    runTPlc,
    runUPlc,
    goldenTPlc,
    goldenTPlcCatch,
    goldenUPlc,
    goldenUPlcCatch,
    goldenTEval,
    goldenUEval,
    goldenTEvalCatch,
    goldenUEvalCatch) where

import           PlutusPrelude

import           Common

import qualified Language.PlutusCore                                        as TPLC
import           Language.PlutusCore.DeBruijn
import qualified Language.PlutusCore.Evaluation.Machine.Cek                 as TPLC
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

import qualified Language.UntypedPlutusCore                                 as UPLC
import qualified Language.UntypedPlutusCore.DeBruijn                        as UPLC
import qualified Language.UntypedPlutusCore.Evaluation.Machine.Cek          as UPLC

import           Control.Exception
import           Control.Monad.Except
import qualified Data.Text.Prettyprint.Doc                                  as PP
import           System.IO.Unsafe

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

pureTry :: Exception e => a -> Either e a
pureTry = unsafePerformIO . try . evaluate

catchAll :: a -> ExceptT SomeException IO a
catchAll value = ExceptT $ try @SomeException (evaluate value)

rethrow :: ExceptT SomeException IO a -> IO a
rethrow = fmap (either throw id) . runExceptT

runTPlc
    :: ( ToTPlc a uni fun, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage,
         uni `Everywhere` PrettyConst, Typeable uni, Typeable fun
       )
    => [a] -> ExceptT SomeException IO (TPLC.EvaluationResult (TPLC.Term TPLC.TyName TPLC.Name uni fun ()))
runTPlc values = do
    ps <- traverse toTPlc values
    let (TPLC.Program _ _ t) = foldl1 TPLC.applyProgram ps
    liftEither $ first toException $ TPLC.extractEvaluationResult $ TPLC.evaluateCek mempty defaultCostModel t

runUPlc
    :: ( ToUPlc a uni fun, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage,
         uni `Everywhere` PrettyConst, Typeable uni, Typeable fun
       )
    => [a] -> ExceptT SomeException IO (UPLC.EvaluationResult (UPLC.Term TPLC.Name uni fun ()))
runUPlc values = do
    ps <- traverse toUPlc values
    let (UPLC.Program _ _ t) = foldl1 UPLC.applyProgram ps
    liftEither $ first toException $ TPLC.extractEvaluationResult $ UPLC.evaluateCek mempty defaultCostModel t

ppCatch :: PrettyPlc a => ExceptT SomeException IO a -> IO (Doc ann)
ppCatch value = either (PP.pretty . show) prettyPlcClassicDebug <$> runExceptT value

ppThrow :: PrettyPlc a => ExceptT SomeException IO a -> IO (Doc ann)
ppThrow value = rethrow $ prettyPlcClassicDebug <$> value

goldenTPlc
    :: (ToTPlc a uni fun, GShow uni, Closed uni, uni `Everywhere` PrettyConst)
     => String -> a -> TestNested
goldenTPlc name value = nestedGoldenVsDocM name $ ppThrow $ do
    p <- toTPlc value
    withExceptT toException $ deBruijnProgram p

goldenTPlcCatch
    :: (ToTPlc a uni fun, GShow uni, Closed uni, uni `Everywhere` PrettyConst)
    => String -> a -> TestNested
goldenTPlcCatch name value = nestedGoldenVsDocM name $ ppCatch $ do
    p <- toTPlc value
    withExceptT toException $ deBruijnProgram p

goldenUPlc
    :: (ToUPlc a uni fun, GShow uni, Closed uni, uni `Everywhere` PrettyConst)
     => String -> a -> TestNested
goldenUPlc name value = nestedGoldenVsDocM name $ ppThrow $ do
    p <- toUPlc value
    withExceptT toException $ UPLC.deBruijnProgram p

goldenUPlcCatch
    :: (ToUPlc a uni fun, GShow uni, Closed uni, uni `Everywhere` PrettyConst)
    => String -> a -> TestNested
goldenUPlcCatch name value = nestedGoldenVsDocM name $ ppCatch $ do
    p <- toUPlc value
    withExceptT toException $ UPLC.deBruijnProgram p

goldenTEval
    :: ( ToTPlc a uni fun, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage, uni `Everywhere` PrettyConst
       , Typeable uni, Typeable fun
       )
    => String -> [a] -> TestNested
goldenTEval name values = nestedGoldenVsDocM name $ prettyPlcClassicDebug <$> (rethrow $ runTPlc values)

goldenUEval
    :: ( ToUPlc a uni fun, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage, uni `Everywhere` PrettyConst
       , Typeable uni, Typeable fun
       )
    => String -> [a] -> TestNested
goldenUEval name values = nestedGoldenVsDocM name $ prettyPlcClassicDebug <$> (rethrow $ runUPlc values)

goldenTEvalCatch
    :: ( ToTPlc a uni fun, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage, uni `Everywhere` PrettyConst
       , Typeable uni, Typeable fun
       )
    => String -> [a] -> TestNested
goldenTEvalCatch name values = nestedGoldenVsDocM name $ ppCatch $ runTPlc values

goldenUEvalCatch
    :: ( ToUPlc a uni fun, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage, uni `Everywhere` PrettyConst
       , Typeable uni, Typeable fun
       )
    => String -> [a] -> TestNested
goldenUEvalCatch name values = nestedGoldenVsDocM name $ ppCatch $ runUPlc values
