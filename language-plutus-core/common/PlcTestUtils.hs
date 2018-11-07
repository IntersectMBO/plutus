{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications      #-}
module PlcTestUtils (
    GetProgram(..),
    catchAll,
    rethrow,
    trivialProgram,
    runPlc,
    goldenPlc,
    goldenPlcCatch,
    goldenEval,
    goldenEvalCatch) where

import           Common

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.CkMachine
import           Language.PlutusCore.Pretty

import           Control.Exception
import           Control.Monad.Except

import qualified Data.Text.Prettyprint.Doc                as PP

-- | Class for ad-hoc overloading of things which can be turned into a PLC program. Any errors
-- from the process should be caught.
class GetProgram a where
    getProgram :: a -> ExceptT SomeException IO (Program TyName Name ())

instance GetProgram a => GetProgram (ExceptT SomeException IO  a) where
    getProgram a = a >>= getProgram

instance GetProgram (Program TyName Name ()) where
    getProgram = pure

catchAll :: a -> ExceptT SomeException IO a
catchAll value = ExceptT $ try @SomeException (evaluate value)

rethrow :: ExceptT SomeException IO a -> IO a
rethrow = fmap (either throw id) . runExceptT

trivialProgram :: Term TyName Name () -> Program TyName Name ()
trivialProgram = Program () (defaultVersion ())

runPlc :: GetProgram a => [a] -> ExceptT SomeException IO EvaluationResult
runPlc values = do
    ps <- traverse getProgram values
    let p = foldl1 applyProgram ps
    catchAll $ runCk p

ppCatch :: PrettyPlc a => ExceptT SomeException IO a -> IO (Doc ann)
ppCatch value = either (PP.pretty . show) prettyPlcClassicDebug <$> runExceptT value

goldenPlc :: GetProgram a => String -> a -> TestNested
goldenPlc name value = nestedGoldenVsDocM name $ prettyPlcClassicDebug <$> (rethrow $ getProgram value)

goldenPlcCatch :: GetProgram a => String -> a -> TestNested
goldenPlcCatch name value = nestedGoldenVsDocM name $ ppCatch $ getProgram value

goldenEval :: GetProgram a => String -> [a] -> TestNested
goldenEval name values = nestedGoldenVsDocM name $ prettyPlcClassicDebug <$> (rethrow $ runPlc values)

goldenEvalCatch :: GetProgram a => String -> [a] -> TestNested
goldenEvalCatch name values = nestedGoldenVsDocM name $ ppCatch $ runPlc values
