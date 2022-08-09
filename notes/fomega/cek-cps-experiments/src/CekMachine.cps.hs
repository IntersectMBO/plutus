-- editorconfig-checker-disable-file

-- This file contains a version of the CEK machine in
-- continuation-passing-style, where the frames and return
-- operation of the original version are replaced with explicit
-- continuations.  The original CEK machine can be seen as a
-- defunctionalised version of this machine.

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

import Data.Text qualified as T
import Data.Text.IO qualified as T
import PlutusCore.Pretty qualified as PLC

import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap

termStr :: Plain Term -> String
termStr = T.unpack . PLC.prettyPlcDefText

type Plain f = f TyName Name ()

-- | A 'Value' packed together with the environment it's defined in.
data Closure = Closure
    { _closureEnvironment :: Environment
    , _closureValue       :: Plain Value
    }

-- | Environments used by the CEK machine.
-- Each row is a mapping from the 'Unique' representing a variable to a 'Closure'.
newtype Environment = Environment (IntMap Closure)

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendEnvironment :: Name () -> Plain Value -> Environment -> Environment -> Environment
extendEnvironment argName arg argEnv (Environment oldEnv) =
    Environment $ IntMap.insert (unUnique $ nameUnique argName) (Closure argEnv arg) oldEnv

-- | Look up a name in an environment.
lookupName :: Name () -> Environment -> Maybe Closure
lookupName name (Environment env) = IntMap.lookup (unUnique $ nameUnique name) env

type Cont = Environment -> Plain Value -> EvaluationResult

computeCek :: Cont -> Environment -> Plain Term -> EvaluationResult
computeCek k env (TyInst _ fun ty) =
    let k' = \e funVal -> instantiateEvaluate k e ty funVal
    in computeCek k' env fun

-- [fun arg] -> compute fun, compute arg, call applyEvaluate; remember fun and arg envs.
computeCek k env (Apply _ fun arg) =
    let k1 = \funEnv funVal ->
             let k2 = \argEnv argVal -> applyEvaluate k funEnv argEnv funVal argVal
             in computeCek k2 env arg
    in computeCek k1 env fun

computeCek k env (Wrap ann tyn ty term) =
    let k' = \e m -> k e (Wrap ann tyn ty m)
    in computeCek k' env term

computeCek k env (Unwrap _ term) =
    let k' = \e v -> case v of
                       Wrap _ _ _ t -> k e t
                       _            -> throw $ MachineException NonWrapUnwrappedMachineError v
    in computeCek k' env term

computeCek k env tyAbs@TyAbs{}       = k env tyAbs
computeCek k env lamAbs@LamAbs{}     = k env lamAbs
computeCek k env constant@Constant{} = k env constant
computeCek _ _ Error{}               = EvaluationFailure
computeCek k env var@(Var _ name)    = case lookupName name env of
    Nothing                  -> throw $ MachineException OpenTermEvaluatedMachineError var
    Just (Closure env' term) -> k env' term

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: Cont -> Environment -> Type TyName () -> Plain Term -> EvaluationResult
instantiateEvaluate k env _  (TyAbs _ _ _ body) = computeCek k env body
instantiateEvaluate k env ty fun
    | isJust $ termAsPrimIterApp fun = k env $ TyInst () fun ty
    | otherwise                      = throw $ MachineException NonPrimitiveInstantiationMachineError fun

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate :: Cont -> Environment -> Environment -> Plain Value -> Plain Value -> EvaluationResult
applyEvaluate k funEnv argEnv lam@(LamAbs _ name _ body) arg =
    computeCek k (extendEnvironment name arg argEnv funEnv) body
applyEvaluate k funEnv _ fun                    arg =
    let term = Apply () fun arg in
        case termAsPrimIterApp term of
            Nothing                       ->
                throw $ MachineException NonPrimitiveApplicationMachineError term
            Just (IterApp headName spine) ->
                case runQuote $ applyBuiltinName headName spine of
                    ConstAppSuccess term' -> k funEnv term'
                    ConstAppFailure       -> EvaluationFailure
                    ConstAppStuck         -> k funEnv term
                    ConstAppError err     -> throw $ MachineException (ConstAppMachineError err) term

-- | Evaluate a term using the CEK machine. May throw a 'MachineException'.
evaluateCek :: Term TyName Name () -> EvaluationResult
evaluateCek = computeCek (\_ v ->  EvaluationSuccess v) (Environment IntMap.empty)

-- | Run a program using the CEK machine. May throw a 'MachineException'.
-- Calls 'evaluateCek' under the hood, so the same caveats apply.
runCek :: Program TyName Name () -> EvaluationResult
runCek (Program _ _ term) = evaluateCek term
