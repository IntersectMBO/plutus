-- | The L machine
-- A lazy machine based on the L machine of Friedman et al. [Improving the Lazy Krivine Machine]
-- More documentation to follow

-- WORK IN PROGRESS

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


-- | A term together with an enviroment mapping free variables to heap locations
data Closure = Closure
    { _closureValue       :: Plain Term
    , _closureEnvironment :: Environment
    } deriving (Show)

-- | A local version of the MachineResult type using closures instead of values
data LMachineResult
    = Success Closure Heap  -- We need both the environment and the heap to see what the value "really" is.
    | Failure

type Plain f = f TyName Name ()

-- L machine environments
-- Each row is a mapping from the 'Unique' representing a variable to a heap location
newtype Environment = Environment (IntMap Loc)
    deriving (Show)

data Frame
    = FrameDelayedArg Closure                    -- Tells the machine that we've got back to N after evaluating M in [M N]
    | FrameMark Environment Loc                  -- Tells the machine that we've finished evaluating a delayed term in the heap
    | FrameTyInstArg (Type TyName ())            -- ^ @{_ A}@
    | FrameUnwrap                                -- ^ @(unwrap _)@
    | FrameWrap () (TyName ()) (Type TyName ())  -- ^ @(wrap α A _)@
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

type Loc = Int -- Heap location. Will Int always be big enough?  maxBound::Int is 2^63-1

{- Environments map variable ids to locations, the heap maps locations
   to terms.  We really do require this indirection: there may be
   multiple objects in the heap corresponding to the same variable
   (during recursion, for example). -}

-- | Look up a heap location in an environment.
lookupLoc :: Name () -> Environment -> Loc
lookupLoc name (Environment env) =
    case IntMap.lookup (unUnique $ nameUnique name) env of
      Nothing  -> error $ "Name not found in environment: " ++ show (nameString name)
                  -- or maybe throw $ MachineException OpenTermEvaluatedMachineError var
                  -- This might be a bit misleading if the error's not due to an open term.
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

-- | Insert a new entry into a heap. The heap grows monotonically with no garbage collection or reuse of heap slots.
insertInHeap :: Closure -> Heap -> (Loc, Heap)
insertInHeap cl (Heap h top) =
    let top' = top + 1
    in (top', Heap (IntMap.insert top' (Unevaluated cl) h) top')

-- | Update the heap entry at a given location.
-- | The old entry presumably persits in the old heap.
modifyHeap :: Loc -> HeapEntry -> Heap -> Heap
modifyHeap l cl (Heap h top) =
    -- Heap (IntMap.adjust (\_ -> cl) l h) top  -- insert or adjust?
    Heap (IntMap.insert l cl h) top
    -- insert seems to be faster than adjust (18s vs 28 s for fib 32) and also uses less memory.

lookupHeap :: Loc -> Heap -> HeapEntry
lookupHeap l (Heap h _) =
    case IntMap.lookup l h of
      Nothing -> error $ "Missing heap location in lookupHeap: " ++ show l
      Just e  -> e

computeL ::EvaluationContext -> Heap -> Closure -> LMachineResult
computeL ctx heap cl@(Closure t env) =
    case t of
      TyInst _ fun ty      -> computeL (FrameTyInstArg ty : ctx)                 heap (Closure fun env) -- fun isn't necessarily a function
      Apply _ fun arg      -> computeL (FrameDelayedArg (Closure arg env) : ctx) heap (Closure fun env)
      Wrap ann tyn ty term -> computeL (FrameWrap ann tyn ty : ctx)              heap (Closure term env)
      Unwrap _ term        -> computeL (FrameUnwrap : ctx)                       heap (Closure term env)
      TyAbs{}              -> returnL ctx heap cl
      LamAbs{}             -> returnL ctx heap cl
      Constant{}           -> returnL ctx heap cl
      Error{}              -> Failure
      Var _ name           -> evalVar ctx heap name env

evalVar :: EvaluationContext -> Heap -> Name() -> Environment -> LMachineResult
evalVar ctx heap name env =
         let l = lookupLoc name env
         in case lookupHeap l heap of
              Evaluated v    -> returnL ctx heap (Closure v env)
              Unevaluated cl -> computeL (FrameMark env l: ctx) heap cl
              -- Reduce the entry to a value, leaving a mark on the stack so we know when we've finished


returnL :: EvaluationContext -> Heap -> Closure -> LMachineResult  -- The closure here should contain a value
returnL [] heap res                                                        = Success res heap
returnL (FrameTyInstArg ty        : ctx) heap cl                           = instantiateEvaluate ctx heap ty cl
returnL (FrameDelayedArg argCl    : ctx) heap cl                           = evaluateFun ctx heap cl argCl
returnL (FrameWrap ann tyn ty     : ctx) heap (Closure v env)              = returnL ctx heap $ Closure (Wrap ann tyn ty v) env
returnL (FrameUnwrap              : ctx) heap (Closure (Wrap _ _ _ t) env) = returnL ctx heap (Closure t env)
returnL (FrameUnwrap              : ctx) _    (Closure term _)             = throw $ MachineException NonWrapUnwrappedMachineError term
returnL (FrameMark env' l         : ctx) heap (Closure v env)              = let heap' = modifyHeap l (Evaluated v) heap
                                                                             in returnL ctx heap' (Closure v env')
                                                                                -- Restore the old environment
                                                                                -- Really? Might we need env again?

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.

evaluateFun :: EvaluationContext -> Heap -> Closure -> Closure-> LMachineResult
evaluateFun ctx heap (Closure fun funEnv) argCl =
    case fun of
      LamAbs _ var _ body ->
          let  (l, heap') = insertInHeap argCl heap
               env9 = updateEnvironment (unUnique $ nameUnique var) l funEnv -- ???
          in computeL ctx heap' (Closure body env9)
      _ ->
          -- We have to force the arguments, which means that we need to get the new heap back as well.
          -- This bit is messy but should be much easier when we have n-ary application for builtins.
          case computeL [] heap argCl of
            Failure -> Failure
            Success (Closure arg' env') heap' ->
                let term = Apply () fun arg'
                in case termAsPrimIterApp term of
                     Nothing ->
                         throw $ MachineException NonPrimitiveApplicationMachineError term
             -- "Cannot reduce a not immediately reducible application."
                     Just (IterApp headName spine) ->
                         case runQuote $ applyBuiltinName headName spine of
                           ConstAppSuccess term' ->  -- trace2 ("Evaluated builtin " ++ (show headName)) $
                                                    returnL ctx heap' (Closure term' funEnv)
                           ConstAppStuck         -> returnL ctx heap' (Closure term funEnv) -- env???
                           ConstAppFailure       -> error $ "ConstAppFailure" ++ show term
                           ConstAppError err     -> throw $ MachineException (ConstAppMachineError err) term


-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate :: EvaluationContext -> Heap -> Type TyName () -> Closure -> LMachineResult
instantiateEvaluate ctx heap ty (Closure fun env) =
    case fun of
      TyAbs _ _ _ body ->
          computeL ctx heap (Closure body env)
      _ -> if isJust $ termAsPrimIterApp fun
           then returnL ctx heap $ Closure (TyInst () fun ty) env
           else throw $ MachineException NonPrimitiveInstantiationMachineError fun

-- | Evaluate a term using the CEK machine. May throw a 'MachineException'.
evaluateL :: Term TyName Name () -> LMachineResult
evaluateL t = computeL [] emptyHeap (Closure t (Environment IntMap.empty))

-- | Run a program using the CEK machine. May throw a 'MachineException'.
-- Calls 'evaluateL' under the hood, so the same caveats apply.
runL :: Program TyName Name () -> EvaluationResult
runL (Program _ _ term) =
    case evaluateL term of
      Success (Closure r _) (Heap m sz) -> trace ("Heap size = " ++ show sz ++ " [" ++ show (IntMap.size m) ++ "]") $ EvaluationSuccess r
      Failure                           -> EvaluationFailure
