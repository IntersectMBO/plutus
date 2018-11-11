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

import           Control.Monad.Except
import           Data.IntMap                                     (IntMap)
import qualified Data.IntMap                                     as IntMap
import qualified Data.Map                                        as Map


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

type Loc = Int -- Heap location. Int should always be big enough: maxBound::Int is 2^63-1

{- Environments map variable ids to locations, the heap maps locations
   to terms.  We really do require this indirection: there may be
   multiple objects in the heap corresponding to the same variable
   (during recursion, for example). -}

-- | Look up a heap location in an environment.
lookupLoc :: Name () -> Environment -> Loc
lookupLoc name (Environment env) =
    case IntMap.lookup (unUnique $ nameUnique name) env of
      Nothing  -> error $ "Name not found in environment: " ++ show (nameString name) ++ "/" ++ show (unUnique $ nameUnique name)
                  -- or maybe throw $ MachineException OpenTermEvaluatedMachineError var
                  -- This might be a bit misleading if the error's not due to an open term.
      Just loc -> loc


data HeapEntry =
    Evaluated   Closure
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
      Just e  -> e
      Nothing -> error $ "Missing heap location in lookupHeap: " ++ show l  -- This should never happen

computeL :: DynamicBuiltinNameMeanings -> EvaluationContext -> Heap -> Closure -> LMachineResult
computeL nms ctx heap cl@(Closure t env) =
    case t of
      TyInst _ fun ty      -> computeL nms (FrameTyInstArg ty : ctx)                 heap (Closure fun env)
      Apply _ fun arg      -> computeL nms (FrameDelayedArg (Closure arg env) : ctx) heap (Closure fun env)
      Wrap ann tyn ty term -> computeL nms (FrameWrap ann tyn ty : ctx)              heap (Closure term env)
      Unwrap _ term        -> computeL nms (FrameUnwrap : ctx)                       heap (Closure term env)
      TyAbs{}              -> returnL  nms ctx heap cl
      LamAbs{}             -> returnL  nms ctx heap cl
      Constant{}           -> returnL  nms ctx heap cl
      Error{}              -> Failure
      Var _ name           -> let l = lookupLoc name env
                              in case lookupHeap l heap of
                                   Evaluated cl   -> returnL nms ctx heap cl
                                   Unevaluated cl ->
                                       case computeL nms [] heap cl
                                       of Success cl' heap' ->
                                              let heap'' = modifyHeap l (Evaluated cl') heap'
                                                  -- Leave this out to make the machine call-by-name (really slow)
                                              in returnL nms ctx heap'' cl'
                                          Failure           -> Failure

-- | Return a closure containing a value. Ideally the fact that we've got a value would be enforced in the (Haskell) types
-- Values still have to be contained in closures.  We could have something like v = \x.y,
-- where y is bound in an environment.  If we ever go on to apply v, we'll need the value of x.

returnL :: DynamicBuiltinNameMeanings -> EvaluationContext -> Heap -> Closure -> LMachineResult
returnL nms [] heap res                                                        = Success res heap
returnL nms (FrameTyInstArg ty        : ctx) heap cl                           = instantiateEvaluate nms ctx heap ty cl
returnL nms (FrameDelayedArg argCl    : ctx) heap cl                           = evaluateFun nms ctx heap cl argCl
returnL nms (FrameWrap ann tyn ty     : ctx) heap (Closure v env)              = returnL nms ctx heap $ Closure (Wrap ann tyn ty v) env
returnL nms (FrameUnwrap              : ctx) heap (Closure (Wrap _ _ _ t) env) = returnL nms ctx heap (Closure t env)
returnL nms (FrameUnwrap              : ctx) _    (Closure term _)             = error "throw $ MachineException NonWrapUnwrappedMachineError term"

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.

evaluateFun :: DynamicBuiltinNameMeanings -> EvaluationContext -> Heap -> Closure -> Closure-> LMachineResult
evaluateFun nms ctx heap (Closure fun funEnv) argCl@(Closure _ argEnv) =
    case fun of
      LamAbs _ var _ body ->
          let (l, heap') = insertInHeap argCl heap
              env' = updateEnvironment (unUnique $ nameUnique var) l funEnv
          in
 -- nameUnique var) ++ " -> " ++ show l ++ ", env = " ++ show env') $
                 computeL nms ctx heap' (Closure body env')

      _ ->
          -- Not a lambda: look for evaluation of a built-in function, possibly with some args already supplied.
          -- We have to force the arguments, which means that we need to get the new heap back as well.
          -- This bit is messy but should be much easier when we have n-ary application for builtins.
          case computeL nms [] heap argCl of
            -- Force the argument, but only at the top level.
            -- This is a bit of a hack.  We're not in the main compute/return process here.
            -- We're preserving ctx, the context at entry, and we'll use that when we return.
            Failure -> Failure
            Success (Closure arg' env') heap' ->
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
                         case runQuote $ applyStagedBuiltinName nms headName spine of
                           ConstAppSuccess term' -> returnL nms ctx heap' (Closure term' funEnv)
                           ConstAppStuck         -> returnL nms ctx heap' (Closure term  funEnv)
                           -- It's arguable what the env should be here. Again that depends on what the built-in can return.
                           -- Ideally it'd always return a closed term, so the environment should be irrelevant.
                           ConstAppFailure       -> error $ "ConstAppFailure" ++ show term
                           ConstAppError err     -> error "throw $ MachineException (ConstAppMachineError err) term"

-- | Look up a 'DynamicBuiltinName'
lookupDynamicBuiltinName :: DynamicBuiltinNameMeanings -> DynamicBuiltinName -> DynamicBuiltinNameMeaning
lookupDynamicBuiltinName nms dynName =
    case Map.lookup dynName (unDynamicBuiltinNameMeanings nms) of
        Nothing   -> error "throw $ MachineException err term" {- where
            err  = OtherMachineError $ UnknownDynamicBuiltinNameError dynName
            term = Constant () $ DynBuiltinName () dynName-}
        Just mean -> mean


applyStagedBuiltinName :: DynamicBuiltinNameMeanings -> StagedBuiltinName -> [Plain Value] -> Quote ConstAppResult
applyStagedBuiltinName nms (DynamicStagedBuiltinName name) args =
    case lookupDynamicBuiltinName nms name of
      DynamicBuiltinNameMeaning sch x -> applyTypeSchemed sch x args
applyStagedBuiltinName nms (StaticStagedBuiltinName  name) args = applyBuiltinName name args


-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate :: DynamicBuiltinNameMeanings -> EvaluationContext -> Heap -> Type TyName () -> Closure -> LMachineResult
instantiateEvaluate nms ctx heap ty (Closure fun env) =
    case fun of
      TyAbs _ _ _ body ->
          computeL nms ctx heap (Closure body env)
      _ -> if isJust $ termAsPrimIterApp fun
           then returnL nms ctx heap $ Closure (TyInst () fun ty) env
           else error "throw $ MachineException NonPrimitiveInstantiationMachineError fun"

-- | Evaluate a term using the L machine. May throw a 'MachineException'.
evaluateL :: DynamicBuiltinNameMeanings -> Term TyName Name () -> LMachineResult
evaluateL nms t = computeL nms [] emptyHeap (Closure t (Environment IntMap.empty))

-- | Run a program using the L machine. May throw a 'MachineException'.
runL :: DynamicBuiltinNameMeanings -> Program TyName Name () -> EvaluationResult
runL nms (Program _ _ term) =
    case evaluateL nms term of
      Success (Closure r e) (Heap _ sz) -> trace ("Heap size = " ++ show sz ++ "\n env = " ++ show e) $ EvaluationSuccess r
      Failure                           -> EvaluationFailure
