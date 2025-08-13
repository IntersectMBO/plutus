{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Evaluation.Builtins.Common
    ( unsafeSplitStructuralOperational
    , evaluateCek
    , evaluateCekNoEmit
    , readKnownCek
    , typecheckAnd
    , typecheckEvaluateCek
    , typecheckEvaluateCekNoEmit
    , typecheckReadKnownCek
    , PlcType
    , PlcTerm
    , UplcTerm
    , TypeErrorOrCekResult (..)
    , evalTerm
    , mkApp1
    , mkApp2
    , ok
    , fails
    , evalOkEq
    , evalOkTrue
    , integer
    , bytestring
    , zero
    , one
    , true
    , false
    , cekSuccessFalse
    , cekSuccessTrue
    )
where

import PlutusCore qualified as TPLC
import PlutusCore.Builtin
import PlutusCore.Compiler.Erase qualified as TPLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Evaluation.Machine.MachineParameters
import PlutusCore.MkPlc (builtin, mkConstant, mkIterAppNoAnn)
import PlutusCore.Name.Unique
import PlutusCore.Pretty
import PlutusCore.TypeCheck
import PlutusPrelude (def)

import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek

import Control.Monad.Except
import Data.Bifunctor
import Data.ByteString (ByteString)
import Data.Text (Text)

import Test.Tasty.QuickCheck (Property, property, (===))

-- | Type check and evaluate a term.
typecheckAnd
    :: ( MonadError (TypeErrorPlc uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , CaseBuiltin uni, Closed uni, uni `Everywhere` ExMemoryUsage
       )
    => BuiltinSemanticsVariant fun
    -> (MachineParameters CekMachineCosts fun (CekValue uni fun ()) ->
            UPLC.Term Name uni fun () -> a)
    -> CostingPart uni fun -> TPLC.Term TyName Name uni fun () -> m a
typecheckAnd semvar action costingPart term = TPLC.runQuoteT $ do
    -- Here we don't use 'getDefTypeCheckConfig', to cover the absurd case where
    -- builtins can change their type according to their 'BuiltinSemanticsVariant'.
    tcConfig <- TypeCheckConfig defKindCheckConfig <$> builtinMeaningsToTypes semvar ()
    _ <- TPLC.inferType tcConfig term
    return . action runtime $ TPLC.eraseTerm term
    where
      runtime = MachineParameters def . mkMachineVariantParameters semvar $
                -- FIXME: make sure we have the the correct cost model for the semantics variant.
                   CostModel defaultCekMachineCostsForTesting costingPart

-- | Type check and evaluate a term, logging enabled.
typecheckEvaluateCek
    :: ( MonadError (TypeErrorPlc uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni, Pretty fun
       , CaseBuiltin uni
       )
    => BuiltinSemanticsVariant fun
    -> CostingPart uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (EvaluationResult (UPLC.Term Name uni fun ()), [Text])
typecheckEvaluateCek semvar =
    typecheckAnd semvar $ \params ->
        first unsafeSplitStructuralOperational . evaluateCek logEmitter params

-- | Type check and evaluate a term, logging disabled.
typecheckEvaluateCekNoEmit
    :: ( MonadError (TypeErrorPlc uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni, Pretty fun
       , CaseBuiltin uni
       )
    => BuiltinSemanticsVariant fun
    -> CostingPart uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (EvaluationResult (UPLC.Term Name uni fun ()))
typecheckEvaluateCekNoEmit semvar =
    typecheckAnd semvar $ \params ->
        unsafeSplitStructuralOperational . evaluateCekNoEmit params

-- | Type check and convert a Plutus Core term to a Haskell value.
typecheckReadKnownCek
    :: ( MonadError (TypeErrorPlc uni fun ()) m, TPLC.Typecheckable uni fun, GEq uni
       , uni `Everywhere` ExMemoryUsage, PrettyUni uni, Pretty fun
       , CaseBuiltin uni
       , ReadKnown (UPLC.Term Name uni fun ()) a
       )
    => BuiltinSemanticsVariant fun
    -> CostingPart uni fun
    -> TPLC.Term TyName Name uni fun ()
    -> m (Either (CekEvaluationException Name uni fun) a)
typecheckReadKnownCek semvar =
    typecheckAnd semvar readKnownCek


-- TPLC/UPLC utilities

type PlcType = TPLC.Type TPLC.TyName TPLC.DefaultUni ()
type PlcTerm  = TPLC.Term TPLC.TyName TPLC.Name TPLC.DefaultUni TPLC.DefaultFun ()
type PlcError = TypeErrorPlc TPLC.DefaultUni TPLC.DefaultFun ()
type UplcTerm = UPLC.Term TPLC.Name TPLC.DefaultUni TPLC.DefaultFun ()

-- Possible CEK evluation results, flattened out
data TypeErrorOrCekResult =
    TypeCheckError PlcError
  | CekError
  | CekSuccess UplcTerm
    deriving stock (Eq, Show)

evalTerm :: PlcTerm -> TypeErrorOrCekResult
evalTerm term =
    case typecheckEvaluateCekNoEmit def defaultBuiltinCostModelForTesting term
    of Left e -> TypeCheckError e
       Right x  ->
           case x of
             TPLC.EvaluationFailure   -> CekError
             TPLC.EvaluationSuccess s -> CekSuccess s

integer :: Integer -> PlcTerm
integer = mkConstant ()

zero :: PlcTerm
zero = integer 0

one :: PlcTerm
one = integer 1

bytestring :: ByteString -> PlcTerm
bytestring = mkConstant ()

true :: PlcTerm
true = mkConstant () True

false :: PlcTerm
false = mkConstant () False

cekSuccessFalse :: TypeErrorOrCekResult
cekSuccessFalse = CekSuccess $ mkConstant () False

cekSuccessTrue :: TypeErrorOrCekResult
cekSuccessTrue = CekSuccess $ mkConstant () True

mkApp1 :: TPLC.DefaultFun -> PlcTerm -> PlcTerm
mkApp1 b x = mkIterAppNoAnn (builtin () b) [x]

mkApp2 :: TPLC.DefaultFun -> PlcTerm -> PlcTerm -> PlcTerm
mkApp2 b x y = mkIterAppNoAnn (builtin () b) [x,y]

-- QuickCheck utilities

-- | Term evaluates successfully
ok :: PlcTerm -> Property
ok t = property $
       case evalTerm t of
         CekSuccess _ -> True
         _            -> False

-- | Term fails to evaluate successfully
fails :: PlcTerm -> Property
fails t = evalTerm t === CekError

-- Check that two terms evaluate successfully and return the same result
evalOkEq :: PlcTerm -> PlcTerm -> Property
evalOkEq t1 t2 =
    case evalTerm t1 of
      r@(CekSuccess _) -> r === evalTerm t2
      _                -> property False

evalOkTrue :: PlcTerm -> Property
evalOkTrue t = evalOkEq t true


