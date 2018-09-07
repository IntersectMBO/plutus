module PlutusCoreInterpreter.CekMachine where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.CkMachine (CkError(..), CkException(..), CkEvalResult(..))
import           Language.PlutusCore.View
import           PlutusPrelude

import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

type Plain f = f TyName Name ()

newtype Environment = Environment
    { unEnvironment :: IntMap (Plain Value, Environment)
    }

data Frame
    = FrameApplyFun Environment (Plain Value)    -- ^ @[V _]@
    | FrameApplyArg Environment (Plain Term)     -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName ())            -- ^ @{_ A}@
    | FrameUnwrap                                -- ^ @(unwrap _)@
    | FrameWrap () (TyName ()) (Type TyName ())  -- ^ @(wrap α A _)@

type Context = [Frame]

extendEnvironment :: Name () -> Plain Value -> Environment -> Environment -> Environment
extendEnvironment argName arg argEnv (Environment oldEnv) =
    Environment $ IntMap.insert (unUnique $ nameUnique argName) (arg, argEnv) oldEnv

lookupName :: Name () -> Environment -> Maybe (Plain Value, Environment)
lookupName name (Environment env) = IntMap.lookup (unUnique $ nameUnique name) env

computeCek :: Environment -> Context -> Plain Term -> CkEvalResult
computeCek env con (TyInst _ fun ty)      = computeCek env (FrameTyInstArg ty : con) fun
computeCek env con (Apply _ fun arg)      = computeCek env (FrameApplyArg env arg : con) fun
computeCek env con (Wrap ann tyn ty term) = computeCek env (FrameWrap ann tyn ty : con) term
computeCek env con (Unwrap _ term)        = computeCek env (FrameUnwrap : con) term
computeCek env con tyAbs@TyAbs{}          = returnCek env con tyAbs
computeCek env con lamAbs@LamAbs{}        = returnCek env con lamAbs
computeCek env con constant@Constant{}    = returnCek env con constant
computeCek _   _   Error{}                = CkEvalFailure
computeCek env con var@(Var _ name)       = case lookupName name env of
    Nothing           -> throw $ CkException OpenTermEvaluatedCkError var
    Just (term, env') -> returnCek env' con term

returnCek :: Environment -> Context -> Plain Value -> CkEvalResult
returnCek _   []                             res = CkEvalSuccess res
returnCek env (FrameTyInstArg ty      : con) fun = instantiateEvaluate env con ty fun
returnCek env (FrameApplyArg env' arg : con) fun = computeCek env' (FrameApplyFun env fun : con) arg
returnCek env (FrameApplyFun env' fun : con) arg = applyEvaluate env' env con fun arg
returnCek env (FrameWrap ann tyn ty   : con) val = returnCek env con $ Wrap ann tyn ty val
returnCek env (FrameUnwrap            : con) dat = case dat of
    Wrap _ _ _ term -> returnCek env con term
    term            -> throw $ CkException NonWrapUnwrappedCkError term

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: Environment -> Context -> Type TyName () -> Plain Term -> CkEvalResult
instantiateEvaluate env con _  (TyAbs _ _ _ body) = computeCek env con body
instantiateEvaluate env con ty fun
    | isJust $ termAsPrimIterApp fun = returnCek env con $ TyInst () fun ty
    | otherwise                      = throw $ CkException NonPrimitiveInstantiationCkError fun

-- | Apply a function to an argument and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate :: Environment -> Environment -> Context -> Plain Value -> Plain Value -> CkEvalResult
applyEvaluate funEnv argEnv con (LamAbs _ name _ body) arg =
    computeCek (extendEnvironment name arg argEnv funEnv) con body
applyEvaluate funEnv _      con fun                    arg =
    let term = Apply () fun arg in
        case termAsPrimIterApp term of
            Nothing                       ->
                throw $ CkException NonPrimitiveApplicationCkError term
            Just (IterApp headName spine) ->
                case applyBuiltinName headName spine of
                    ConstAppSuccess term' -> returnCek funEnv con term'
                    ConstAppFailure       -> CkEvalFailure
                    ConstAppStuck         -> returnCek funEnv con term
                    ConstAppError err     -> throw $ CkException (ConstAppCkError err) term

-- | Evaluate a term using the CEK machine. May throw a 'CkException'.
evaluateCek :: Term TyName Name () -> CkEvalResult
evaluateCek = computeCek (Environment IntMap.empty) []

-- | Run a program using the CK machine. May throw a 'CkException'.
-- Calls 'evaluateCk' under the hood, so the same caveats apply.
runCek :: Program TyName Name () -> CkEvalResult
runCek (Program _ _ term) = evaluateCek term
