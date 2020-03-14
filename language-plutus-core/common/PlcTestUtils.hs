{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module PlcTestUtils (
    GetProgram(..),
    pureTry,
    catchAll,
    rethrow,
    trivialProgram,
    runPlc,
    goldenPlc,
    goldenPlcCatch,
    goldenEval,
    goldenEvalCatch) where

import           PlutusPrelude

import           Common

import           Language.PlutusCore
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Pretty

import           Control.Exception
import           Control.Monad.Except
import qualified Data.Text.Prettyprint.Doc                       as PP
import           System.IO.Unsafe

-- | Class for ad-hoc overloading of things which can be turned into a PLC program. Any errors
-- from the process should be caught.
class GetProgram a uni | a -> uni where
    getProgram :: a -> ExceptT SomeException IO (Program TyName Name uni ())

instance GetProgram a uni => GetProgram (ExceptT SomeException IO a) uni where
    getProgram a = a >>= getProgram

instance GetProgram (Program TyName Name uni ()) uni where
    getProgram = pure

pureTry :: Exception e => a -> Either e a
pureTry = unsafePerformIO . try . evaluate

catchAll :: a -> ExceptT SomeException IO a
catchAll value = ExceptT $ try @SomeException (evaluate value)

rethrow :: ExceptT SomeException IO a -> IO a
rethrow = fmap (either throw id) . runExceptT

trivialProgram :: Term TyName Name uni () -> Program TyName Name uni ()
trivialProgram = Program () (defaultVersion ())

runPlc
    :: ( GetProgram a uni, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage, uni `Everywhere` Pretty, Typeable uni
       )
    => [a] -> ExceptT SomeException IO (EvaluationResultDef uni)
runPlc values = do
    ps <- traverse getProgram values
    let p = foldl1 applyProgram ps
    liftEither . first toException . extractEvaluationResult . evaluateCek mempty $ toTerm p

ppCatch :: PrettyPlc a => ExceptT SomeException IO a -> IO (Doc ann)
ppCatch value = either (PP.pretty . show) prettyPlcClassicDebug <$> runExceptT value

ppThrow :: PrettyPlc a => ExceptT SomeException IO a -> IO (Doc ann)
ppThrow value = rethrow $ prettyPlcClassicDebug <$> value

goldenPlc
    :: (GetProgram a uni, GShow uni, Closed uni, uni `Everywhere` Pretty)
     => String -> a -> TestNested
goldenPlc name value = nestedGoldenVsDocM name $ ppThrow $ do
    p <- getProgram value
    withExceptT toException $ deBruijnProgram p

goldenPlcCatch
    :: (GetProgram a uni, GShow uni, Closed uni, uni `Everywhere` Pretty)
    => String -> a -> TestNested
goldenPlcCatch name value = nestedGoldenVsDocM name $ ppCatch $ do
    p <- getProgram value
    withExceptT toException $ deBruijnProgram p

goldenEval
    :: ( GetProgram a uni, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage, uni `Everywhere` Pretty, Typeable uni
       )
    => String -> [a] -> TestNested
goldenEval name values = nestedGoldenVsDocM name $ prettyPlcClassicDebug <$> (rethrow $ runPlc values)

goldenEvalCatch
    :: ( GetProgram a uni, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage, uni `Everywhere` Pretty, Typeable uni
       )
    => String -> [a] -> TestNested
goldenEvalCatch name values = nestedGoldenVsDocM name $ ppCatch $ runPlc values
