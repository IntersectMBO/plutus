-- | The CEK machine.
-- Rules are the same as for the CK machine except we do not use substitution and use
-- environments instead.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names. This is for efficiency reasons.
-- The type checker pass is a prerequisite.
-- Feeding ill-typed terms to the CEK machine will likely result in a 'MachineException'.
-- The CEK machine generates booleans along the way which might contain globally non-unique 'Unique's.
-- This is not a problem as the CEK machines handles name capture by design.
-- Dynamic extensions to the set of built-ins are allowed.
-- In case an unknown dynamic built-in is encountered, an 'UnknownDynamicBuiltinNameError' is returned
-- (wrapped in 'OtherMachineError').

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.PlutusCore.Evaluation.Machine.Cek
    ( CekMachineException
    , EvaluationResult (..)
    , EvaluationResultDef
    , evaluateCek
    , unsafeEvaluateCek
    , readKnownCek
    , runCek
    , unsafeRunCek
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Name
import           Language.PlutusCore.View
import           PlutusPrelude

import           Control.Lens.TH                                  (makeLenses)
import Control.Lens.Setter
import           Control.Monad.Except
import qualified Data.Map                                         as Map
import Control.Monad.RWS.Strict
import Data.Tuple.Select
import Data.HashMap.Monoidal
import Language.PlutusCore.Evaluation.Machine.GenericSemigroup
import Foreign.Storable
import qualified Data.Text                             as T
import qualified Data.ByteString.Lazy           as BSL

import Language.PlutusCore.Evaluation.Machine.ExMemory


-- | The CEK machine-specific 'MachineException'.
type CekMachineException = MachineException UnknownDynamicBuiltinNameError

-- | A 'Value' packed together with the environment it's defined in.
data Closure = Closure
    { _closureVarEnv :: VarEnv
    , _closureValue  :: WithMemory Value
    }

-- | Variable environments used by the CEK machine.
-- Each row is a mapping from the 'Unique' representing a variable to a 'Closure'.
type VarEnv = UniqueMap TermUnique Closure

-- | The environment the CEK machine runs in.
data CekEnv = CekEnv
    { _cekEnvMeans  :: DynamicBuiltinNameMeanings
    , _cekEnvVarEnv :: VarEnv
    , _cekEnvProtocolParameters :: ()
    }

data ExBudget = ExBudget { _exBudgetCPU :: ExCPU, _exBudgetMemory :: ExMemory }

makeLenses ''ExBudget

-- | The monad the CEK machine runs in.
type CekMBase w s = ExceptT CekMachineException (RWS CekEnv w s)
type SpendExUnits w s = (SpendExUnitsState s, SpendExUnitsWriter w)
type CekM w s a = SpendExUnits w s => CekMBase w s a

data ExTally = ExTally
    { _exTallyCPU :: MonoidalHashMap (Plain Term) [ExCPU]
    , _exTallyMemory :: MonoidalHashMap (Plain Term) [ExMemory]
    }
    deriving stock (Eq, Generic)
    deriving (Semigroup, Monoid) via (GenericSemigroupMonoid ExTally)

spendBoth :: WithMemory Term -> ExCPU -> ExMemory -> CekM w s ()
spendBoth term cpu mem = spendCPU term cpu >> spendMemory term mem

spendMemory :: WithMemory Term -> ExMemory -> CekM w s ()
spendMemory term mem = do
    spendSMemory term mem
    spendWMemory term mem

spendCPU :: WithMemory Term -> ExCPU -> CekM w s ()
spendCPU term mem = do
    spendSCPU term mem
    spendWCPU term mem

class Monoid w => SpendExUnitsWriter w where
    spendWMemory :: forall s. WithMemory Term -> ExMemory -> CekMBase w s ()
    spendWCPU :: forall s. WithMemory Term -> ExCPU -> CekMBase w s ()

instance SpendExUnitsWriter () where
    spendWMemory _ _ = pure ()
    spendWCPU _ _ = pure ()

class SpendExUnitsState s where
    spendSMemory :: forall w. Monoid w => (WithMemory Term) -> ExMemory -> CekMBase w s ()
    spendSCPU :: forall w. Monoid w => (WithMemory Term) -> ExCPU -> CekMBase w s ()

instance SpendExUnitsState () where
    spendSCPU _ _ = pure ()
    spendSMemory _ _ = pure ()

spendSBudget :: Ord a => Num a => Monoid w => Lens' ExBudget a -> WithMemory Term -> a -> CekMBase w ExBudget ()
spendSBudget l term ex = do
    newEx <- fmap (\x -> x - ex) $ gets (view l)
    if newEx < 0 then
        throwError $ MachineException OutOfExError (void term)
    else
        assign l newEx

instance SpendExUnitsState ExBudget where
    spendSCPU = spendSBudget exBudgetCPU
    spendSMemory = spendSBudget exBudgetMemory

data Frame
    = FrameApplyFun VarEnv (WithMemory Value)               -- ^ @[V _]@
    | FrameApplyArg VarEnv (WithMemory Term)                -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName ExMemory)                  -- ^ @{_ A}@
    | FrameUnwrap                                      -- ^ @(unwrap _)@
    | FrameIWrap ExMemory (Type TyName ExMemory) (Type TyName ExMemory)  -- ^ @(iwrap A B _)@

type Context = [Frame]

makeLenses ''CekEnv

runCekM :: SpendExUnits w s => CekEnv -> s -> CekM w s a -> (Either CekMachineException a, s, w)
runCekM r s cekm = runRWS (runExceptT cekm) r s

-- | Get the current 'VarEnv'.
getVarEnv :: CekM w s VarEnv
getVarEnv = asks _cekEnvVarEnv

-- | Set a new 'VarEnv' and proceed.
withVarEnv :: VarEnv -> CekM w s a -> CekM w s a
withVarEnv venv = mapExceptT (local (set cekEnvVarEnv venv))

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendVarEnv :: Name ExMemory -> WithMemory Value -> VarEnv -> VarEnv -> VarEnv
extendVarEnv argName arg argVarEnv = insertByName argName $ Closure argVarEnv arg

-- | Look up a variable name in the environment.
lookupVarName :: Name ExMemory -> CekM w s Closure
lookupVarName varName = do
    varEnv <- getVarEnv
    case lookupName varName varEnv of
        Nothing   -> throwError $ MachineException OpenTermEvaluatedMachineError (Var () (void varName))
        Just clos -> pure clos

-- | Look up a 'DynamicBuiltinName' in the environment.
lookupDynamicBuiltinName :: DynamicBuiltinName -> CekM w s DynamicBuiltinNameMeaning
lookupDynamicBuiltinName dynName = do
    DynamicBuiltinNameMeanings means <- asks _cekEnvMeans
    case Map.lookup dynName means of
        Nothing   -> throwError $ MachineException err term where
            err  = OtherMachineError $ UnknownDynamicBuiltinNameErrorE dynName
            term = Builtin () $ DynBuiltinName () dynName
        Just mean -> pure mean

-- | The computing part of the CEK machine.
-- Either
-- 1. adds a frame to the context and calls 'computeCek' ('TyInst', 'Apply', 'IWrap', 'Unwrap')
-- 2. calls 'returnCek' on values ('TyAbs', 'LamAbs', 'Constant')
-- 3. returns 'EvaluationFailure' ('Error')
-- 4. looks up a variable in the environment and calls 'returnCek' ('Var')
computeCek :: Context -> WithMemory Term -> CekM w s EvaluationResultDef
computeCek con t@(TyInst _ body ty)       = do
    spendBoth t 1 1
    computeCek (FrameTyInstArg ty : con) body
computeCek con t@(Apply _ fun arg)        = do
    spendBoth t 1 1
    varEnv <- getVarEnv
    computeCek (FrameApplyArg varEnv arg : con) fun
computeCek con t@(IWrap ann pat arg term) = do
    spendBoth t 1 1
    computeCek (FrameIWrap ann pat arg : con) term
computeCek con t@(Unwrap _ term)          = do
    spendBoth t 1 1
    computeCek (FrameUnwrap : con) term
computeCek con tyAbs@TyAbs{}            = returnCek con tyAbs
computeCek con lamAbs@LamAbs{}          = returnCek con lamAbs
computeCek con constant@Constant{}      = returnCek con constant
computeCek con bi@Builtin{}             = returnCek con bi
computeCek _   Error{}                  = pure EvaluationFailure
computeCek con t@(Var _ varName)          = do
    spendBoth t 1 1
    Closure newVarEnv term <- lookupVarName varName
    withVarEnv newVarEnv $ returnCek con term

-- | The returning part of the CEK machine.
-- Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
-- from the context and either
-- 1. performs reduction and calls 'computeCek' ('FrameTyInstArg', 'FrameApplyFun', 'FrameUnwrap')
-- 2. performs a constant application and calls 'returnCek' ('FrameTyInstArg', 'FrameApplyFun')
-- 3. puts 'FrameApplyFun' on top of the context and proceeds with the argument from 'FrameApplyArg'
-- 4. grows the resulting term ('FrameWrap')
returnCek :: Context -> WithMemory Value -> CekM w s EvaluationResultDef
returnCek []                                  res = pure $ EvaluationSuccess (void res)
returnCek (FrameTyInstArg ty           : con) fun = do
    spendBoth fun 1 1 -- TODO
    instantiateEvaluate con ty fun
returnCek (FrameApplyArg argVarEnv arg : con) fun = do
    spendBoth fun 1 1 -- TODO
    funVarEnv <- getVarEnv
    withVarEnv argVarEnv $ computeCek (FrameApplyFun funVarEnv fun : con) arg
returnCek (FrameApplyFun funVarEnv fun : con) arg = do
    spendBoth arg 1 1 -- TODO maybe builtin to the applying anyway?
    argVarEnv <- getVarEnv
    applyEvaluate funVarEnv argVarEnv con fun arg
returnCek (FrameIWrap ann pat arg      : con) val = do
    spendBoth val 1 1 -- TODO
    returnCek con $ IWrap ann pat arg val
returnCek (FrameUnwrap                 : con) dat = do
    spendBoth dat 1 1 -- TODO
    case dat of
        IWrap _ _ _ term -> returnCek con term
        term             -> throwError $ MachineException NonWrapUnwrappedMachineError (void term)

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate :: Context -> Type TyName ExMemory -> WithMemory Term -> CekM w s EvaluationResultDef
instantiateEvaluate con _  (TyAbs _ _ _ body) = computeCek con body
instantiateEvaluate con ty fun
    | isJust $ termAsPrimIterApp fun = returnCek con $ TyInst 1 fun ty -- TODO
    | otherwise                      =
        throwError $ MachineException NonPrimitiveInstantiationMachineError (void fun)

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate
    :: VarEnv -> VarEnv -> Context -> WithMemory Value -> WithMemory Value -> CekM w s EvaluationResultDef
applyEvaluate funVarEnv argVarEnv con (LamAbs _ name _ body) arg =
    withVarEnv (extendVarEnv name arg argVarEnv funVarEnv) $ computeCek con body
applyEvaluate funVarEnv _         con fun                    arg =
    let term = Apply 1 fun arg in -- TODO
        case termAsPrimIterApp term of
            Nothing                       ->
                throwError $ MachineException NonPrimitiveApplicationMachineError (void term)
            Just (IterApp headName spine) -> do
                constAppResult <- applyStagedBuiltinName arg headName spine
                withVarEnv funVarEnv $ case constAppResult of
                    ConstAppSuccess res -> computeCek con res
                    ConstAppFailure     -> pure EvaluationFailure
                    ConstAppStuck       -> returnCek con term
                    ConstAppError   err ->
                        throwError $ MachineException (ConstAppMachineError err) (void term)

evaluateInCekM :: EvaluateConstApp (ExceptT CekMachineException (RWS CekEnv w s)) a -> CekM w s (ConstAppResult a)
evaluateInCekM a = do
    let eval means' term = local (over cekEnvMeans (mappend means')) $ computeCek [] (annotateMemory term)
    runEvaluateConstApp eval a

-- TODO invalid number of args
estimateStaticStagedCost :: BuiltinName -> [WithMemory Value] -> (ExCPU, ExMemory)
estimateStaticStagedCost AddInteger [x, y] = (1, 1)
estimateStaticStagedCost SubtractInteger [x, y] = (1, 1)
estimateStaticStagedCost MultiplyInteger [x, y] = (1, 1)
estimateStaticStagedCost DivideInteger [x, y] = (1, 1)
estimateStaticStagedCost QuotientInteger [x, y] = (1, 1)
estimateStaticStagedCost RemainderInteger [x, y] = (1, 1)
estimateStaticStagedCost ModInteger [x, y] = (1, 1)
estimateStaticStagedCost LessThanInteger [x, y] = (1, 1)
estimateStaticStagedCost LessThanEqInteger [x, y] = (1, 1)
estimateStaticStagedCost GreaterThanInteger [x, y] = (1, 1)
estimateStaticStagedCost GreaterThanEqInteger [x, y] = (1, 1)
estimateStaticStagedCost EqInteger [x, y] = (1, 1)
estimateStaticStagedCost Concatenate [x, y] = (1, 1)
estimateStaticStagedCost TakeByteString [x, y] = (1, 1)
estimateStaticStagedCost DropByteString [x, y] = (1, 1)
estimateStaticStagedCost SHA2 x = (1, 1)
estimateStaticStagedCost SHA3 x = (1, 1)
estimateStaticStagedCost VerifySignature [x, y] = (1, 1)
estimateStaticStagedCost EqByteString [x, y] = (1, 1)
estimateStaticStagedCost LtByteString [x, y] = (1, 1)
estimateStaticStagedCost GtByteString [x, y] = (1, 1)
estimateStaticStagedCost _ _ = (0, 0) -- TODO

-- | Apply a 'StagedBuiltinName' to a list of 'Value's.
applyStagedBuiltinName :: WithMemory Value -> StagedBuiltinName -> [WithMemory Value] -> CekM w s (ConstAppResult (WithMemory Term))
applyStagedBuiltinName arg (DynamicStagedBuiltinName name) args = do
    -- TODO estimate costing here
    DynamicBuiltinNameMeaning sch x <- lookupDynamicBuiltinName name
    fmap (fmap (fmap (const 1))) $ evaluateInCekM $ applyTypeSchemed sch x (fmap void args)
applyStagedBuiltinName arg (StaticStagedBuiltinName name) args = do
    let (cpu, memory) = estimateStaticStagedCost name args
    spendBoth arg cpu memory
    fmap (fmap (fmap (const memory))) $ evaluateInCekM $ applyBuiltinName name (fmap void args)

-- | Evaluate a term in an environment using the CEK machine.
evaluateCekIn
    :: SpendExUnits w s => CekEnv -> s -> WithMemory Term -> (Either CekMachineException EvaluationResultDef, s, w)
evaluateCekIn cekEnv s = runCekM cekEnv s . computeCek []

-- | Evaluate a term using the CEK machine.
evaluateCek
    :: forall w s. SpendExUnits w s => DynamicBuiltinNameMeanings -> s -> Plain Term -> (Either CekMachineException EvaluationResultDef, s, w)
evaluateCek means s term = evaluateCekIn (CekEnv means mempty mempty) s $ annotateMemory term

-- | Evaluate a term using the CEK machine. May throw a 'CekMachineException'.
unsafeEvaluateCek :: DynamicBuiltinNameMeanings -> Term TyName Name () -> EvaluationResultDef
unsafeEvaluateCek dyn term = either throw id $ (sel1 $ evaluateCek @() dyn () term)

-- The implementation is a bit of a hack.
-- And used in tests only. Not doing costing for now.
readKnownCek
    :: KnownType a
    => DynamicBuiltinNameMeanings
    -> Term TyName Name ()
    -> Either CekMachineException (EvaluationResult a)
readKnownCek means term = do
    res <- runReflectT $ readKnown (\m -> sel1 . evaluateCek @() @() (mappend means m) ()) term
    case res of
        EvaluationFailure            -> Right EvaluationFailure
        EvaluationSuccess (Left err) -> Left $ MachineException appErr term where
            appErr = ConstAppMachineError $ UnreadableBuiltinConstAppError term err
        EvaluationSuccess (Right x)  -> Right $ EvaluationSuccess x

-- | Run a program using the CEK machine.
-- Calls 'evaluateCekCatch' under the hood.
runCek :: SpendExUnits w s => DynamicBuiltinNameMeanings -> s -> Program TyName Name () ->
    (Either CekMachineException EvaluationResultDef, s, w)
runCek means s (Program _ _ term) = evaluateCek means s term

-- | Run a program using the CEK machine. May throw a 'CekMachineException'.
-- Calls 'evaluateCek' under the hood.
unsafeRunCek :: DynamicBuiltinNameMeanings -> Program TyName Name () -> EvaluationResultDef
unsafeRunCek means (Program _ _ term) = unsafeEvaluateCek means term
