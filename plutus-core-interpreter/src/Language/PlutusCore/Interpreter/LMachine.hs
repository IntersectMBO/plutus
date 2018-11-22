-- | The L machine
-- A lazy machine based on the L machine of Friedman et al. [Improving the Lazy Krivine Machine]
-- For more details see the document in plutus/docs/fomega/lazy-machine
-- The code here's closely based on the CEK machine implementation.

-- The main difference from the CEK machine is that we have a heap
-- containing closures containing evaluated/unevaluated function
-- arguments, and environments mapping variable IDs to heap locations.
-- To evaluate [M N], we save a closure C containing N and the current
-- environment in a stack frame, then evaluate M to get a value
-- (lambda/builtin) like \x.e and an environment env.  We retrieve the
-- argument closure C from the stack, generate a new heap location l,
-- bind C (unevaluated) to l in the heap, then evaluate e in
-- env[x->l].  When we come across a use of x inside e, we look up l
-- in the heap to get N (inside the closure C): if it's Evaluated then
-- we continue immediately, using N instead of x. Otherwise we place
-- an update marker on the stack and evaluate N to get a new closure
-- C' containing a value V (and a possibly new environment): by
-- this time we should be back at the update marker containing l, and
-- we store Evaluated C back in the heap at l, then continue
-- evaluating e.


module Language.PlutusCore.Interpreter.LMachine
    ( EvaluationResultF (EvaluationSuccess, EvaluationFailure)
    , EvaluationResult
    , evaluateL
    , runL
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.MachineException
import           Language.PlutusCore.View
import           PlutusPrelude

import           Data.IntMap                                     (IntMap)
import qualified Data.IntMap                                     as IntMap
import qualified Data.Map                                        as Map

type Plain f = f TyName Name ()


-- | A term together with an enviroment mapping free variables to heap locations
data Closure = Closure
    { _closureValue       :: Plain Term
    , _closureEnvironment :: Environment
    } deriving (Show)

-- | L machine environments
-- Each row is a mapping from the 'Unique' representing a variable to a heap location
newtype Environment = Environment (IntMap HeapLoc)
    deriving (Show)

-- | Heap location. Int should always be big enough: maxBound::Int is 2^63-1
type HeapLoc = Int

-- | Heap entries: unevaluated and evaluated lazy function arguments.
data HeapEntry =
    Evaluated   Closure  -- The term in this closure should always be a value. It would be good if the type system could distiniguish these.
  | Unevaluated Closure

-- | The heap itself: a map from heap locations to
-- unevaluated/evaluated terms, together with an integer counter
-- @_top@ which serves as the current heap location.
data Heap = Heap {
      _heap :: IntMap HeapEntry
    , _top  :: Int
}

{- Environments map variable ids to locations, the heap maps locations
   to terms.  We really do require this indirection: there may be
   multiple objects in the heap corresponding to the same variable
   (during recursion, for example).  For the same reason we always
   work with closures instead of terms; this also makes it easier
   to ensure that we're using the correct environment. -}


-- | Stack frames.  These are effectively continuations: would using explicit CPS speed things up?
-- The spec also has a frame for n-ary built in application, but that's not in the AST yet
data Frame
    = FrameAppArg Closure                        -- ^ @[_ N]@       -- Tells the machine that we've got back to N after evaluating M in [M N]
    | FrameHeapUpdate HeapLoc                    -- ^ @(update l)@  -- Mark the stack for evaluation of a delayed argument
    | FrameTyInstArg (Type TyName ())            -- ^ @{_ A}@
    | FrameUnwrap                                -- ^ @(unwrap _)@
    | FrameWrap () (TyName ()) (Type TyName ())  -- ^ @(wrap α A _)@
      deriving (Show)

-- | A context is a stack of frames.
type EvaluationContext = [Frame]

-- | A local version of the EvaluationResult type using closures instead of values
data LMachineResult
    = Success Closure Heap  -- We need both the environment and the heap to see what the value "really" is.
    | Failure

-- | Extend an environment with a new binding
updateEnvironment :: Int -> HeapLoc -> Environment -> Environment
updateEnvironment index cl (Environment m) = Environment (IntMap.insert index cl m)

-- | Look up a heap location in an environment.
lookupHeapLoc :: Name () -> Environment -> HeapLoc
lookupHeapLoc name (Environment env) =
    case IntMap.lookup (unUnique $ nameUnique name) env of
      Nothing  -> error $ "Name not found in environment: " ++ show (nameString name) ++ "/" ++ show (unUnique $ nameUnique name)
                  -- or maybe throw $ MachineException OpenTermEvaluatedMachineError var
                  -- This might be a bit misleading if the error's not due to an open term.
      Just loc -> loc


emptyHeap :: Heap
emptyHeap = Heap IntMap.empty 0

-- | Insert a new entry into a heap. The heap grows monotonically with no garbage collection or reuse of heap slots.
insertInHeap :: Closure -> Heap -> (HeapLoc, Heap)
insertInHeap cl (Heap h top) =
    let top' = top + 1
    in (top', Heap (IntMap.insert top' (Unevaluated cl) h) top')

-- | Replace the heap entry at a given location.
-- The old entry presumably persits in the old heap.
updateHeap :: HeapLoc -> HeapEntry -> Heap -> Heap
updateHeap l cl (Heap h top) =
    Heap (IntMap.insert l cl h) top
    -- insert seems to be faster than adjust (18s vs 28 s for fib 32) and also uses less memory.

lookupHeap :: HeapLoc -> Heap -> HeapEntry
lookupHeap l (Heap h _) =
    case IntMap.lookup l h of
      Just e  -> e
      Nothing -> error $ "Missing heap location in lookupHeap: " ++ show l  -- This should never happen


-- | The basic computation step of the L machine.  Search down the AST looking for a value, saving surrounding contexts on the stack.
computeL :: DynamicBuiltinNameMeanings -> EvaluationContext -> Heap -> Closure -> LMachineResult
computeL dbnms ctx heap cl@(Closure term env) =
    case term of
      TyInst _ fun ty      -> computeL dbnms (FrameTyInstArg ty : ctx)                 heap (Closure fun env)
      Apply _ fun arg      -> computeL dbnms (FrameAppArg (Closure arg env) : ctx)     heap (Closure fun env)
      Wrap ann tyn ty term -> computeL dbnms (FrameWrap ann tyn ty : ctx)              heap (Closure term env)
      Unwrap _ term        -> computeL dbnms (FrameUnwrap : ctx)                       heap (Closure term env)
      TyAbs{}              -> returnL  dbnms ctx heap cl
      LamAbs{}             -> returnL  dbnms ctx heap cl
      Builtin{}            -> returnL  dbnms ctx heap cl
      Constant{}           -> returnL  dbnms ctx heap cl
      Error{}              -> Failure
      Var _ name           -> let l = lookupHeapLoc name env
                              in case lookupHeap l heap of
                                   Evaluated cl'   -> returnL dbnms ctx heap cl'
                                   Unevaluated cl' -> computeL dbnms (FrameHeapUpdate l : ctx) heap cl'


-- | Return a closure containing a value. Ideally the fact that we've
-- got a value would be enforced in the (Haskell) types Values still
-- have to be contained in closures.  We could have something like @v
-- = \x.y@, where @y@y is bound in an environment.  If we ever go on
-- to apply @v@, we'll need the value of @x@.
returnL :: DynamicBuiltinNameMeanings -> EvaluationContext -> Heap -> Closure -> LMachineResult
returnL _ [] heap res                                                          = Success res heap
returnL dbnms (FrameTyInstArg ty        : ctx) heap cl                           = instantiateEvaluate dbnms ctx heap ty cl
returnL dbnms (FrameAppArg argClosure   : ctx) heap cl                           = evaluateFun dbnms ctx heap cl argClosure
returnL dbnms (FrameWrap ann tyn ty     : ctx) heap (Closure v env)              = returnL dbnms ctx heap $ Closure (Wrap ann tyn ty v) env
returnL dbnms (FrameHeapUpdate l        : ctx) heap cl                           = returnL dbnms ctx heap' cl
                                                                                   where heap' = updateHeap l (Evaluated cl) heap
                                                                                      -- Leave this out to make the machine call-by-name (really slow)
returnL dbnms (FrameUnwrap              : ctx) heap (Closure (Wrap _ _ _ t) env) = returnL dbnms ctx heap (Closure t env)
returnL     _ (FrameUnwrap              : _)      _ (Closure term env)           = throw $ MachineException NonWrapUnwrappedMachineError term


-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.

evaluateFun :: DynamicBuiltinNameMeanings -> EvaluationContext -> Heap -> Closure -> Closure-> LMachineResult
evaluateFun dbnms ctx heap (Closure fun funEnv) argClosure =
    case fun of
      LamAbs _ var _ body ->
          let (l, heap') = insertInHeap argClosure heap
              env' = updateEnvironment (unUnique $ nameUnique var) l funEnv
          in  computeL dbnms ctx heap' (Closure body env')

      _ ->
          -- Not a lambda: look for evaluation of a built-in function, possibly with some args already supplied.
          -- We have to force the arguments, which means that we need to get the new heap back as well.
          -- This bit is messy but should be much easier when we have n-ary application for builtins.
          case computeL dbnms [] heap argClosure of
            -- Force the argument, but only at the top level.
            -- This is a bit of a hack.  We're not in the main compute/return process here.
            -- We're preserving ctx, the context at entry, and we'll use that when we return.
            -- We could also add a new type of stack frame for this.
            Failure -> Failure
            Success (Closure arg' _env') heap' ->
                -- FIXME: we're throwing away env' here, but we have to because the builtin interface doesn't know
                -- about environments.  Maybe we should substitute in the stuff in the enviroment to get a closed term,
                -- but that decision will have to wait until we know what the final interface is.
                -- See https://github.com/input-output-hk/plutus/blob/master/language-plutus-core/docs/Constant%20application.md
                let term = Apply () fun arg'
                in case termAsPrimIterApp term of
                     Nothing ->
                         error "throw $ MachineException NonPrimitiveApplicationMachineError term"
                               -- "Cannot reduce a not immediately reducible application."  This message isn't too informative.
                     Just (IterApp headName spine) ->
                         case runQuote $ applyStagedBuiltinName dbnms headName spine of
                           ConstAppSuccess term' -> returnL dbnms ctx heap' (Closure term' funEnv)
                           ConstAppStuck         -> returnL dbnms ctx heap' (Closure term  funEnv)
                           -- It's arguable what the env should be here. Again that depends on what the built-in can return.
                           -- Ideally it'd always return a closed term, so the environment should be irrelevant.
                           ConstAppFailure       -> error $ "ConstAppFailure" ++ show term
                           ConstAppError _err    -> error "throw $ MachineException (ConstAppMachineError err) term"

-- | Look up a 'DynamicBuiltinName'
lookupDynamicBuiltinName :: DynamicBuiltinNameMeanings -> DynamicBuiltinName -> DynamicBuiltinNameMeaning
lookupDynamicBuiltinName dbnms dynName =
    case Map.lookup dynName (unDynamicBuiltinNameMeanings dbnms) of
        Nothing   -> error "throw $ MachineException err term" {- where
            err  = OtherMachineError $ UnknownDynamicBuiltinNameError dynName
            term = Constant () $ DynBuiltinName () dynName-}
        Just mean -> mean

-- | Apply a staged built-in name to a list of values
applyStagedBuiltinName :: DynamicBuiltinNameMeanings -> StagedBuiltinName -> [Plain Value] -> Quote ConstAppResult
applyStagedBuiltinName dbnms (DynamicStagedBuiltinName name) args =
    case lookupDynamicBuiltinName dbnms name of
      DynamicBuiltinNameMeaning sch x -> applyTypeSchemed sch x args
applyStagedBuiltinName _dbnms (StaticStagedBuiltinName  name) args = applyBuiltinName name args


-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate :: DynamicBuiltinNameMeanings -> EvaluationContext -> Heap -> Type TyName () -> Closure -> LMachineResult
instantiateEvaluate dbnms ctx heap ty (Closure fun env) =
    case fun of
      TyAbs _ _ _ body ->
          computeL dbnms ctx heap (Closure body env)
      _ -> if isJust $ termAsPrimIterApp fun
           then returnL dbnms ctx heap $ Closure (TyInst () fun ty) env
           else error "throw $ MachineException NonPrimitiveInstantiationMachineError fun"

-- | Evaluate a term using the L machine. This internal version returns a result
-- containing the final heap and environment, which you might need to know. For example,
-- it could be useful for testing to know how big the heap is.  Also, if we want to
-- return a value to whatever has invoked the machine we may want to fully expand it,
-- and you'd need the environment and heap to do that.
evaluateL_internal :: DynamicBuiltinNameMeanings -> Term TyName Name () -> LMachineResult
evaluateL_internal dbnms t = computeL dbnms [] emptyHeap (Closure t (Environment IntMap.empty))

-- | Evaluate a term using the L machine. May throw a 'MachineException'.
evaluateL :: DynamicBuiltinNameMeanings -> Term TyName Name () -> EvaluationResult
evaluateL dbnms t = case evaluateL_internal dbnms t of
      Success (Closure r _) (Heap _ _) -> EvaluationSuccess r
      Failure                          -> EvaluationFailure

-- | Run a program using the L machine. May throw a 'MachineException'.
runL :: DynamicBuiltinNameMeanings -> Program TyName Name () -> EvaluationResult
runL dbnms (Program _ _ term) = evaluateL dbnms term
