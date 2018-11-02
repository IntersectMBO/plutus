-- | The CEK machine.
-- Rules are the same as for the CK machine from "Language.PlutusCore.Evaluation.CkMachine",
-- except we do not use substitution and use environments instead.
-- The CEK machine relies on variables having non-equal 'Unique's whenever they have non-equal
-- string names. I.e. 'Unique's are used instead of string names, so the renamer pass is required.
-- This is for efficiency reasons.
-- The type checker pass is required as well (and in our case it subsumes the renamer pass).
-- Feeding ill-typed terms to the CEK machine will likely result in a 'MachineException'.
-- The CEK machine generates booleans along the way which might contain globally non-unique 'Unique's.
-- This is not a problem as the CEK machines handles name capture by design.

module Language.PlutusCore.Interpreter.LMachine
    ( EvaluationResult (..)
    , evaluateL
    , runL
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.MachineException (MachineError (..), MachineException (..))
import           Language.PlutusCore.Evaluation.Result           (EvaluationResult (..))
import           Language.PlutusCore.View
import           PlutusPrelude

import           Data.IntMap                                     (IntMap)
import qualified Data.IntMap                                     as IntMap

type Plain f = f TyName Name ()

-- | A 'Value' packed together with the environment it's defined in.
data Closure = Closure
    { _closureValue       :: Plain Value
    , _closureEnvironment :: Environment
    }

-- | Environments used by the CEK machine.
-- Each row is a mapping from the 'Unique' representing a variable to a heap location
newtype Environment = Environment (IntMap Loc)
    deriving (Show)

data Frame
    = FrameDelayedArg (Plain Term) Environment
    | FrameTyInstArg (Type TyName ())            -- ^ @{_ A}@
    | FrameUnwrap                                -- ^ @(unwrap _)@
    | FrameWrap () (TyName ()) (Type TyName ())  -- ^ @(wrap α A _)@
    | FrameMark Environment Loc
      deriving (Show)

{- Suppose we come to [M N]: we want to save N and the current
   environment, then evaluate M to get a value (lambda/builtin) like \x.e
   and an environment env.  We generate a new heap location l, bind N
   (unevaluated) to l in the heap, then evaluate e in env[x->l].

   When we come across a use of x inside e, we look up l in the heap
   to get N, evaluate it to get a value v, store v back in the heap at l,
   then continue evaluating e.
 -}

type EvaluationContext = [Frame]

emptyEnvironment :: Environment
emptyEnvironment = Environment IntMap.empty

updateEnvironment :: Int -> Loc -> Environment -> Environment
updateEnvironment index cl (Environment m) = Environment (IntMap.insert index cl m)

-- | Extend an environment with a variable name, the value the variable stands for
-- and the environment the value is defined in.
{-
extendEnvironment :: Name () -> Plain Value -> Environment -> Environment -> Environment
extendEnvironment argName arg argEnv (Environment oldEnv) =
    Environment $ IntMap.insert (unUnique $ nameUnique argName) (Closure arg argEnv) oldEnv
-}

{-
-- | Look up a name in an environment.
lookupName :: Name () -> Environment -> Maybe Closure
lookupName name (Environment env) = IntMap.lookup (unUnique $ nameUnique name) env
-}

type Loc = Int -- Heap location. Will Int always be big enough?  maxBound::Int is 2^63-1

-- | Look up a heap location in an environment.
lookupLoc :: Name () -> Environment -> Loc
lookupLoc name (Environment env) =
    case IntMap.lookup (unUnique $ nameUnique name) env of
      Nothing  -> error $ "Name not found in environment: " ++ show (nameString name)
      Just loc -> loc

data HeapEntry =
    Evaluated (Plain Term) -- Should really be Value
  | Unevaluated Closure

data Heap = Heap {
      _heap :: IntMap HeapEntry
    , _top  :: Int
}

emptyHeap :: Heap
emptyHeap = Heap IntMap.empty 0

insertInHeap :: Closure -> Heap -> (Loc, Heap)
insertInHeap cl (Heap h top) =
    let top' = top + 1
    in (top', Heap (IntMap.insert top' (Unevaluated cl) h) top')

modifyHeap :: Loc -> HeapEntry -> Heap -> Heap
modifyHeap l cl (Heap h top) =
    Heap (IntMap.insert l cl h) top

lookupHeap :: Loc -> Heap -> HeapEntry
lookupHeap l (Heap h _) =
    case IntMap.lookup l h of
      Nothing -> error $ "Missing heap location in lookupHeap: " ++ show l
      Just e  -> e

-- | The computing part of the CEK machine.
-- Either
-- 1. adds a frame to the context and calls 'computeCek' ('TyInst', 'Apply', 'Wrap', 'Unwrap')
-- 2. calls 'returnCek' on values ('TyAbs', 'LamAbs', 'Constant')
-- 3. returns 'EvaluationFailure' ('Error')
-- 4. looks up a variable in the environment and calls 'returnCek' ('Var')
computeL :: Heap -> Environment -> EvaluationContext -> Plain Term -> EvaluationResult
computeL heap env ctx (TyInst _ fun ty)      = computeL heap env (FrameTyInstArg ty : ctx) fun      -- fun isn't necesaarily a function
computeL heap env ctx (Apply _ fun arg)      = computeL heap env (FrameDelayedArg arg env: ctx) fun
computeL heap env ctx (Wrap ann tyn ty term) = computeL heap env (FrameWrap ann tyn ty : ctx) term
computeL heap env ctx (Unwrap _ term)        = computeL heap env (FrameUnwrap : ctx) term
computeL heap env ctx tyAbs@TyAbs{}          = returnL heap env ctx tyAbs
computeL heap env ctx lamAbs@LamAbs{}        = returnL heap env ctx lamAbs
computeL heap env ctx constant@Constant{}    = returnL heap env ctx constant
computeL _ _   _   Error{}                   = EvaluationFailure
computeL heap env ctx var@(Var _ name)       = let l = lookupLoc name env
                                               in case lookupHeap l heap of
                                                    Evaluated v -> returnL heap env ctx v
                                                    Unevaluated (Closure term env') ->
--                                                        trace ("Unevaluated: " ++ show term) $
  --                                                      trace ("env: " ++ show env') $
                                                        computeL heap env' (FrameMark env l: ctx) term -- CHECK THE ENVS
                                                        -- reduce the entry to a value, leaving a mark on
                                                        -- the stack so we know when we've finished
{--
    Nothing                  -> throw $ MachineException OpenTermEvaluatedMachineError var
    Just (Closure term env') -> returnL env' ctx term
---}

-- | The returning part of the CEK machine.
-- Returns 'EvaluationSuccess' in case the context is empty, otherwise pops up one frame
-- from the context and either
-- 1. performs reduction and calls 'computeL' ('FrameTyInstArg', 'FrameApplyFun', 'FrameUnwrap')
-- 2. performs a constant application and calls 'returnL' ('FrameTyInstArg', 'FrameApplyFun')
-- 3. puts 'FrameApplyFun' on top of the context and proceeds with the argument from 'FrameApplyArg'
-- 4. grows the resulting term ('FrameWrap')
returnL :: Heap -> Environment -> EvaluationContext -> Plain Value -> EvaluationResult
returnL _ _ []                                    res = EvaluationSuccess res
returnL heap env (FrameTyInstArg ty        : ctx) fun = instantiateEvaluate heap env ctx ty fun
returnL heap env (FrameDelayedArg arg env' : ctx) val = evaluateFun heap ctx val env arg env'
returnL heap env (FrameWrap ann tyn ty     : ctx) val = returnL heap env ctx $ Wrap ann tyn ty val
returnL heap env (FrameUnwrap              : ctx) dat = case dat of
    Wrap _ _ _ term -> returnL heap env ctx term
    term            -> throw $ MachineException NonWrapUnwrappedMachineError term
returnL heap env (FrameMark env' l: ctx) val = returnL heap env' ctx val -- Restore the old environment

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.

evaluateFun :: Heap -> EvaluationContext -> Plain Term -> Environment -> Plain Term -> Environment -> EvaluationResult
evaluateFun heap ctx (LamAbs _ var _ body) funEnv arg argEnv =
    let (l, heap') = insertInHeap (Closure arg argEnv) heap
        env9 = updateEnvironment (unUnique $ nameUnique var) l funEnv -- ???
    in computeL heap' env9 ctx body
evaluateFun heap ctx fun funEnv arg argEnv =
-- We have to force the arguments, which means that we need to get the new heap back as well. ****************
   case computeL heap argEnv [] arg of
     EvaluationFailure -> EvaluationFailure
     EvaluationSuccess arg' ->
         let term = Apply () fun arg'
         in case termAsPrimIterApp term of
              Nothing ->
                  throw $ MachineException NonPrimitiveApplicationMachineError term
                  -- "Cannot reduce a not immediately reducible application."
              Just (IterApp headName spine) ->
                  case runQuote $ applyBuiltinName headName spine of
                    ConstAppSuccess term' -> returnL heap funEnv ctx term'
                    ConstAppStuck         -> returnL heap funEnv ctx term
                    ConstAppFailure       -> error $ "ConstAppFailure" ++ show term
                    ConstAppError err     -> throw $ MachineException (ConstAppMachineError err) term


-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: Heap -> Environment -> EvaluationContext -> Type TyName () -> Plain Term -> EvaluationResult
instantiateEvaluate heap env ctx _  (TyAbs _ _ _ body) = computeL heap env ctx body
instantiateEvaluate heap env ctx ty fun
    | isJust $ termAsPrimIterApp fun = returnL heap env ctx $ TyInst () fun ty
    | otherwise                      = throw $ MachineException NonPrimitiveInstantiationMachineError fun

-- | Evaluate a term using the CEK machine. May throw a 'MachineException'.
evaluateL :: Term TyName Name () -> EvaluationResult
evaluateL = computeL emptyHeap (Environment IntMap.empty) []

-- | Run a program using the CEK machine. May throw a 'MachineException'.
-- Calls 'evaluateL' under the hood, so the same caveats apply.
runL :: Program TyName Name () -> EvaluationResult
runL (Program _ _ term) = evaluateL term
