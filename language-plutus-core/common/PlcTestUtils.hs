{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications  #-}
module PlcTestUtils (
    GetProgram(..),
    catchAll,
    getProgramCatch,
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

-- | Class for ad-hoc overloading of things which can be turned into a PLC program. Any errors in the
-- process should be thrown, allowing clients to decide whether to have them terminate the test or
-- catch them.
class GetProgram a where
    getProgram :: a -> Program TyName Name ()

instance GetProgram (Program TyName Name ()) where
    getProgram = id

instance GetProgram (Term TyName Name ()) where
    getProgram = trivialProgram

catchAll :: a -> ExceptT SomeException IO a
catchAll value = ExceptT $ try @SomeException (evaluate value)

getProgramCatch :: GetProgram a => a -> ExceptT SomeException IO (Program TyName Name ())
getProgramCatch value = catchAll $ getProgram value

trivialProgram :: Term TyName Name () -> Program TyName Name ()
trivialProgram = Program () (defaultVersion ())

runPlc :: GetProgram a => [a] -> EvaluationResult
runPlc values =
    let ps = fmap getProgram values
        p = foldl1 applyProgram ps
    in runCk p

ppCatch :: PrettyPlc a => ExceptT SomeException IO a -> IO (Doc ann)
ppCatch value = either (PP.pretty . show) prettyPlcClassicDebug <$> runExceptT value

goldenPlc :: GetProgram a => String -> a -> TestNested
goldenPlc name value = nestedGoldenVsDoc name $ prettyPlcClassicDebug $ getProgram value

goldenPlcCatch :: GetProgram a => String -> a -> TestNested
goldenPlcCatch name value = nestedGoldenVsDocM name $ ppCatch $ getProgramCatch value

goldenEval :: GetProgram a => String -> [a] -> TestNested
goldenEval name values = nestedGoldenVsDoc name $ prettyPlcClassicDebug $ runPlc values

goldenEvalCatch :: GetProgram a => String -> [a] -> TestNested
goldenEvalCatch name values = nestedGoldenVsDocM name $ ppCatch $ catchAll $ runPlc values
