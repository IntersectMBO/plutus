-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns #-}

-- This file contains a version of the CEK machine in
-- implemented as a simple recursie evaluator, with
-- a lot of !s inserted to (hopefully) make sure that
-- we're evaluating the code eagerly.  This can also
-- be regarded as the CPS version with continuations
-- converted back into ordinary function calls.


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
import PlutusCore.Pretty qualified as PLC

import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap

termStr :: Plain Term -> String
termStr = T.unpack . PLC.prettyPlcDefText

type Plain f = f TyName Name ()

-- | A 'Value' packed together with the environment it's defined in.
data Closure = Closure
    { _closureValue       :: Plain Value
    , _closureEnvironment :: Environment
    }

-- | Environments used by the CEK machine.
-- Each row is a mapping from the 'Unique' representing a variable to a 'Closure'.
newtype Environment = Environment (IntMap Closure)

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
extendEnvironment :: Name () -> Plain Value -> Environment -> Environment -> Environment
extendEnvironment argName arg argEnv (Environment oldEnv) =
    Environment $ IntMap.insert (unUnique $ nameUnique argName) (Closure arg argEnv) oldEnv

-- | Look up a name in an environment.
lookupName :: Name () -> Environment -> Maybe Closure
lookupName name (Environment env) = IntMap.lookup (unUnique $ nameUnique name) env


evalCek :: Closure -> Closure
evalCek !cl@(Closure term env) =
--    trace ("eval: " ++ termStr term) $
    case term of
      TyAbs{} -> cl
      LamAbs{} -> cl
      Constant{} -> cl

      TyInst _ fun ty -> instantiateEvaluate ty $ evalCek (Closure fun env)

      Apply _ fun arg -> applyEvaluate (evalCek $ Closure fun env) (evalCek $ Closure arg env)

      Wrap ann tyname ty term' ->
          let Closure term2 env2 = evalCek $ Closure term' env
          in  Closure (Wrap ann tyname ty term2) env2

      Unwrap _ term' ->
             case evalCek $ Closure term' env of
               Closure (Wrap _ _ _ t) env' -> evalCek $ Closure t env'
               _                           -> throw $ MachineException NonWrapUnwrappedMachineError term'

      Error{} -> throw $ MachineException OpenTermEvaluatedMachineError term

      Var _ name -> case lookupName name env of
                      Nothing                     -> throw $ MachineException OpenTermEvaluatedMachineError term
                      Just cl@(Closure val7 env7) -> cl

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: Type TyName () -> Closure -> Closure
instantiateEvaluate _  !(Closure (TyAbs _ _ _ body) env) = evalCek (Closure body env)
instantiateEvaluate ty !(Closure fun env)
    | isJust $! termAsPrimIterApp fun = Closure (TyInst () fun ty) env
    | otherwise                      = throw $ MachineException NonPrimitiveInstantiationMachineError fun

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate :: Closure -> Closure -> Closure
applyEvaluate !(Closure funVal funEnv) !(Closure argVal argEnv) =
    case funVal of
      LamAbs _ name _ body -> evalCek $ Closure body (extendEnvironment name argVal argEnv funEnv)

      _ -> let !term = Apply () funVal argVal in
           case termAsPrimIterApp term of
            Nothing                       ->
                throw $ MachineException NonPrimitiveApplicationMachineError term
            Just (IterApp headName spine) ->
                case runQuote $! ((applyBuiltinName $! headName) $! spine) of
                    ConstAppSuccess term' -> Closure term' funEnv
                    ConstAppFailure       -> throw $ MachineException OpenTermEvaluatedMachineError term
                    ConstAppStuck         -> Closure term funEnv
                    ConstAppError err     -> throw $ MachineException (ConstAppMachineError err) term

-- | Evaluate a term using the CEK machine. May throw a 'MachineException'.
evaluateCek :: Term TyName Name () -> EvaluationResult
evaluateCek !term =
    let Closure result _ = evalCek $! Closure term (Environment IntMap.empty)
    in EvaluationSuccess result

-- | Run a program using the CEK machine. May throw a 'MachineException'.
-- Calls 'evaluateCek' under the hood, so the same caveats apply.
runCek :: Program TyName Name () -> EvaluationResult
runCek !(Program _ _ term) = evaluateCek term
