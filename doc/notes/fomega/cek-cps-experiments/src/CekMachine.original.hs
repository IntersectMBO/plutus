-- editorconfig-checker-disable-file
-- | The CEK machine.
-- Rules are the same as for the CK machine from "PlutusCore.Evaluation.CkMachine",
-- except we do not use substitution and use environments instead.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names, so the renamer pass is required.
-- This is for efficiency reasons.
-- The type checker pass is required as well (and in our case it subsumes the renamer pass).
-- Feeding ill-typed terms to the CEK machine will likely result in a 'MachineException'.
-- The CEK machine generates booleans along the way which might contain globally non-unique 'Unique's.
-- This is not a problem as the CEK machines handles name capture by design.

module PlutusCore.Interpreter.CekMachine
    ( EvaluationResult (..)
    , evaluateCek
    , runCek
    ) where

import PlutusCore
import PlutusCore.Constant
import PlutusCore.Evaluation.MachineException (MachineError (..), MachineException (..))
import PlutusCore.Evaluation.Result (EvaluationResult (..))
import PlutusCore.View
import PlutusPrelude

import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap

type Plain f = f TyName Name ()

-- | A 'Value' packed together with the environment it's defined in.
data Closure = Closure
    { _closureEnvironment :: Environment
    , _closureValue       :: Plain Value
    }

-- | Environments used by the CEK machine.
-- Each row is a mapping from the 'Unique' representing a variable to a 'Closure'.
newtype Environment = Environment (IntMap Closure)

data Frame
    = FrameApplyFun Environment (Plain Value)    -- ^ @[V _]@
    | FrameApplyArg Environment (Plain Term)     -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName ())            -- ^ @{_ A}@
    | FrameUnwrap                                -- ^ @(unwrap _)@
    | FrameWrap () (TyName ()) (Type TyName ())  -- ^ @(wrap α A _)@

type Context = [Frame]

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendEnvironment :: Name () -> Plain Value -> Environment -> Environment -> Environment
extendEnvironment argName arg argEnv (Environment oldEnv) =
    Environment $ IntMap.insert (unUnique $ nameUnique argName) (Closure argEnv arg) oldEnv

-- | Look up a name in an environment.
lookupName :: Name () -> Environment -> Maybe Closure
lookupName name (Environment env) = IntMap.lookup (unUnique $ nameUnique name) env

-- | The computing part of the CEK machine.
-- Either
-- 1. adds a frame to the context and calls 'computeCek' ('TyInst', 'Apply', 'Wrap', 'Unwrap')
-- 2. calls 'returnCek' on values ('TyAbs', 'LamAbs', 'Constant')
-- 3. returns 'EvaluationFailure' ('Error')
-- 4. looks up a variable in the environment and calls 'returnCek' ('Var')
computeCek :: Environment -> Context -> Plain Term -> EvaluationResult
computeCek env con (TyInst _ fun ty)      = computeCek env (FrameTyInstArg ty : con) fun
computeCek env con (Apply _ fun arg)      = computeCek env (FrameApplyArg env arg : con) fun
computeCek env con (Wrap ann tyn ty term) = computeCek env (FrameWrap ann tyn ty : con) term
computeCek env con (Unwrap _ term)        = computeCek env (FrameUnwrap : con) term
computeCek env con tyAbs@TyAbs{}          = returnCek env con tyAbs
computeCek env con lamAbs@LamAbs{}        = returnCek env con lamAbs
computeCek env con constant@Constant{}    = returnCek env con constant
computeCek _   _   Error{}                = EvaluationFailure
computeCek env con var@(Var _ name)       = case lookupName name env of
    Nothing                  -> throw $ MachineException OpenTermEvaluatedMachineError var
    Just (Closure env' term) -> returnCek env' con term

-- | The returning part of the CEK machine.
-- Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
-- from the context and either
-- 1. performs reduction and calls 'computeCek' ('FrameTyInstArg', 'FrameApplyFun', 'FrameUnwrap')
-- 2. performs a constant application and calls 'returnCek' ('FrameTyInstArg', 'FrameApplyFun')
-- 3. puts 'FrameApplyFun' on top of the context and proceeds with the argument from 'FrameApplyArg'
-- 4. grows the resulting term ('FrameWrap')
returnCek :: Environment -> Context -> Plain Value -> EvaluationResult
returnCek _   []                             res = EvaluationSuccess res
returnCek env (FrameTyInstArg ty      : con) fun = instantiateEvaluate env con ty fun
returnCek env (FrameApplyArg env' arg : con) fun = computeCek env' (FrameApplyFun env fun : con) arg
returnCek env (FrameApplyFun env' fun : con) arg = applyEvaluate env' env con fun arg
returnCek env (FrameWrap ann tyn ty   : con) val = returnCek env con $ Wrap ann tyn ty val
returnCek env (FrameUnwrap            : con) dat = case dat of
    Wrap _ _ _ term -> returnCek env con term
    term            -> throw $ MachineException NonWrapUnwrappedMachineError term

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: Environment -> Context -> Type TyName () -> Plain Term -> EvaluationResult
instantiateEvaluate env con _  (TyAbs _ _ _ body) = computeCek env con body
instantiateEvaluate env con ty fun
    | isJust $ termAsPrimIterApp fun = returnCek env con $ TyInst () fun ty
    | otherwise                      = throw $ MachineException NonPrimitiveInstantiationMachineError fun

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate :: Environment -> Environment -> Context -> Plain Value -> Plain Value -> EvaluationResult
applyEvaluate funEnv argEnv con (LamAbs _ name _ body) arg =
    computeCek (extendEnvironment name arg argEnv funEnv) con body
applyEvaluate funEnv _      con fun                    arg =
    let term = Apply () fun arg in
        case termAsPrimIterApp term of
            Nothing                       ->
                throw $ MachineException NonPrimitiveApplicationMachineError term
            Just (IterApp headName spine) ->
                case runQuote $ applyBuiltinName headName spine of
                    ConstAppSuccess term' -> returnCek funEnv con term'
                    ConstAppFailure       -> EvaluationFailure
                    ConstAppStuck         -> returnCek funEnv con term
                    ConstAppError err     -> throw $ MachineException (ConstAppMachineError err) term

-- | Evaluate a term using the CEK machine. May throw a 'MachineException'.
evaluateCek :: Term TyName Name () -> EvaluationResult
evaluateCek = computeCek (Environment IntMap.empty) []

-- | Run a program using the CEK machine. May throw a 'MachineException'.
-- Calls 'evaluateCek' under the hood, so the same caveats apply.
runCek :: Program TyName Name () -> EvaluationResult
runCek (Program _ _ term) = evaluateCek term
