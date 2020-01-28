{-# LANGUAGE OverloadedStrings #-}

-- | The L machine
-- A lazy machine based on the L machine of Friedman et al. [Improving the Lazy Krivine Machine]
-- For more details see the document in plutus/docs/fomega/lazy-machine
-- The code here's closely based on the CEK machine implementation.

-- ## Things to fix soon.
--  # Generalise the machine return type so that we can return extra information,
--    like the environment and/or heap.  These are just discarded at the moment.
--  # Deal properly with dynamic builtins.
--  # Monadify some things (heap, dbnms)
--  # Remove the bit where it tries to force arguments to builtins;
--    Roman's new infrastructure should be able to handle this.
--  # Use something more efficient for the heap, like a mutable vector.

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


module Language.PlutusCore.Evaluation.Machine.L
    ( EvaluationResult (..)
    , EvaluationResultDef
    , LMachineError (..)
    , LMachineException
    , LEvaluationException
    , evaluateL
    , unsafeEvaluateL
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Name
import           Language.PlutusCore.View
import           PlutusPrelude

import           Data.IntMap                                      (IntMap)
import qualified Data.IntMap                                      as IntMap

type Plain f = f TyName Name ()



-- | Errors specific to the L machine
data LMachineError
    = LocationNotInHeap HeapLoc
    | VariableNotInHeap
    | NoDynamicBuiltinsYet  -- Temporary

type LMachineException = MachineException LMachineError
type LEvaluationException = EvaluationException LMachineError ()

-- | The monad the L machine runs in.
type LM = Either LEvaluationException

instance Pretty LMachineError where
    pretty (LocationNotInHeap l) = "Location" <+> pretty l <+> "does not exist in the heap"
    pretty VariableNotInHeap     = "Variable not found in the heap"
    pretty NoDynamicBuiltinsYet  = "The L machine cannot currently deal with dynamic built-in functions."


-- | A term together with an enviroment mapping free variables to heap locations
data Closure = Closure
    { _closureValue       :: Plain Term
    , _closureEnvironment :: Environment
    } deriving (Show)

-- | L machine environments
-- Each entry is a mapping from the 'Unique' representing a variable to a heap location
-- Some kind of vector might be more efficient than a map.
newtype Environment = Environment (UniqueMap TermUnique HeapLoc)
    deriving (Show, Semigroup, Monoid)

-- | Heap location. Int gives us at least 2^32 = 4,294,967,296 different values
-- (and 2^64 on a 64-bit machine) which should be big enough.
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
    , _top  :: HeapLoc
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
    = FrameAppArg Closure                              -- ^ @[_ N]@
                                                       -- Tells the machine that we've got back to N after evaluating M in [M N]
    | FrameHeapUpdate HeapLoc                          -- ^ @(update l)@
                                                       -- Mark the stack for evaluation of a delayed argument
    | FrameTyInstArg (Type TyName ())                  -- ^ @{_ A}@
    | FrameUnwrap                                      -- ^ @(unwrap _)@
    | FrameIWrap () (Type TyName ()) (Type TyName ())  -- ^ @(iwrap A B _)@
      deriving (Show)

-- | A context is a stack of frames.
type EvaluationContext = [Frame]

-- | A local version of the EvaluationResult type using closures instead of values.
-- We need both the environment and the heap to see what the value "really" is.
type LMachineResult = (Closure, Heap)

-- | Extend an environment with a new binding
updateEnvironment :: Name () -> HeapLoc -> Environment -> Environment
updateEnvironment name cl (Environment m) = Environment (insertByName name cl m)

-- | Look up a heap location in an environment.
lookupHeapLoc :: Name () -> Environment -> LM HeapLoc
lookupHeapLoc name (Environment env) =
    case lookupName name env of
      Nothing  -> throwingWithCause _MachineError
          (OtherMachineError VariableNotInHeap)
          (Just $ Var () name)
      Just loc -> pure loc

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

lookupHeap :: HeapLoc -> Heap -> LM HeapEntry
lookupHeap l (Heap h _) =
    case IntMap.lookup l h of
      Just e  -> pure e
      Nothing -> throwingWithCause _MachineError (OtherMachineError $ LocationNotInHeap l) Nothing


-- | The basic computation step of the L machine.  Search down the AST looking for a value, saving surrounding contexts on the stack.
computeL :: EvaluationContext -> Heap -> Closure -> LM LMachineResult
computeL ctx heap cl@(Closure term env) =
    case term of
      TyInst _ fun ty         -> computeL (FrameTyInstArg ty : ctx)             heap (Closure fun env)
      Apply _ fun arg         -> computeL (FrameAppArg (Closure arg env) : ctx) heap (Closure fun env)
      IWrap ann pat arg term' -> computeL (FrameIWrap ann pat arg : ctx)        heap (Closure term' env)
      Unwrap _ term'          -> computeL (FrameUnwrap : ctx)                   heap (Closure term' env)
      TyAbs{}                 -> returnL  ctx heap cl
      LamAbs{}                -> returnL  ctx heap cl
      Builtin{}               -> returnL  ctx heap cl
      Constant{}              -> returnL  ctx heap cl
      Error{}                 -> throwingWithCause _EvaluationError (UserEvaluationError ()) Nothing
      Var _ name              -> do
          l <- lookupHeapLoc name env
          e <- lookupHeap l heap
          case e of
              Evaluated cl'   -> returnL ctx heap cl'
              Unevaluated cl' -> computeL (FrameHeapUpdate l : ctx) heap cl'


-- | Return a closure containing a value. Ideally the fact that we've
-- got a value would be enforced in the (Haskell) type. Values still
-- have to be contained in closures.  We could have something like
-- @v= \x.y@, where @y@ is bound in an environment.  If we ever go on
-- to apply @v@, we'll need the value of @y@.
returnL :: EvaluationContext -> Heap -> Closure -> LM LMachineResult
returnL [] heap res = pure (res, heap)
returnL (frame : ctx) heap result@(Closure v env) =
    case frame of
      FrameHeapUpdate l      -> returnL ctx heap' result where heap' = updateHeap l (Evaluated result) heap
      FrameAppArg argClosure -> evaluateFun ctx heap result argClosure
      FrameTyInstArg ty      -> instantiateEvaluate ctx heap ty result
      FrameIWrap ann pat arg -> returnL ctx heap $ Closure (IWrap ann pat arg v) env
      FrameUnwrap            -> case v of
                                  IWrap _ _ _ t -> returnL ctx heap (Closure t env)
                                  _             ->
                                    throwingWithCause _MachineError NonWrapUnwrappedMachineError $ Just v


-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.

evaluateFun :: EvaluationContext -> Heap -> Closure -> Closure-> LM LMachineResult
evaluateFun ctx heap (Closure fun funEnv) argClosure =
    case fun of
      LamAbs _ var _ body ->
          let (l, heap') = insertInHeap argClosure heap
              env' = updateEnvironment var l funEnv
          in  computeL ctx heap' (Closure body env')

      _ -> do
          -- Not a lambda: look for evaluation of a built-in function, possibly with some args already supplied.
          -- We have to force the arguments, which means that we need to get the new heap back as well.
          -- This bit is messy but should be much easier when we have n-ary application for builtins.
          (Closure arg' env', heap') <- computeL [] heap argClosure
              -- Force the argument, but only at the top level.
              -- This is a bit of a hack.  We're not in the main compute/return process here.
              -- We're preserving ctx, the context at entry, and we'll use that when we return.
              -- We could also add a new type of stack frame for this.  Exactly what we do will
              -- depend on the final interface to builtins.
          let term = Apply () fun arg'
          case termAsPrimIterApp term of
            Nothing ->
                throwingWithCause _MachineError NonPrimitiveInstantiationMachineError $ Just term
                -- Was "Cannot reduce a not immediately reducible application."  This message isn't very helpful.
            Just (IterApp (StaticStagedBuiltinName name) spine) -> do
                constAppResult <- applyEvaluateBuiltinName heap' env' name spine
                case constAppResult of
                  ConstAppSuccess term' -> computeL ctx heap' (Closure term' funEnv)
                  -- The spec has return above, but compute seems more sensible.
                  ConstAppStuck         -> returnL ctx heap' (Closure term  funEnv)
                  -- It's arguable what the env should be here. That depends on what the built-in can return.
                  -- Ideally it'd always return a closed term, so the environment should be irrelevant.
            Just (IterApp DynamicStagedBuiltinName{}     _    ) ->
                throwingWithCause _MachineError (OtherMachineError NoDynamicBuiltinsYet) $ Just term


applyEvaluateBuiltinName :: Heap -> Environment -> BuiltinName -> [Value TyName Name ()] -> LM (ConstAppResult ())
applyEvaluateBuiltinName heap env = runApplyBuiltinName (const $ evalL heap env)

evalL :: Heap -> Environment -> Plain Term -> LM (Plain Term)
evalL heap env term = translateResult $ computeL [] heap (Closure term env)
-- I'm not sure if this is doing quite the right thing.  The current
-- strategy of the dynamic interface is that it when you're evaluating
-- a builtin, you also pass the current PLC evaluator along with its
-- state so that the builtin can evaluate terms properly (for example,
-- it may need to look up a variable in an environment).  It's
-- possible that this could update the heap, but in this case we're
-- not getting the new heap back.  I think this is harmless, but
-- perhaps inefficient (we may have to re-evaluate something that
-- we've already evaluated).  We could solve this by putting the heap
-- in a suitable monad, but let's wait until the interface has
-- stabilised first.  I think the version above is OK for simple
-- builtins for the time being.


-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate :: EvaluationContext -> Heap -> Type TyName () -> Closure -> LM LMachineResult
instantiateEvaluate ctx heap ty (Closure fun env) =
    case fun of
      TyAbs _ _ _ body ->
          computeL ctx heap (Closure body env)
      _ -> if isJust $ termAsPrimIterApp fun
           then returnL ctx heap $ Closure (TyInst () fun ty) env
           else throwingWithCause _MachineError NonPrimitiveInstantiationMachineError $ Just fun

-- | Evaluate a term using the L machine. This internal version
-- returns a result containing the final heap and environment, which
-- it mightbe useful to know (for example, if we're testing we might
-- want to know how big the heap is.  Also, if we want to return a
-- value to whatever has invoked the machine we may want to fully
-- expand it, and you'd need the environment and heap to do that.
internalEvaluateL :: Term TyName Name () -> LM LMachineResult
internalEvaluateL t = computeL [] emptyHeap (Closure t mempty)


-- | Convert an L machine result into the standard result type for communication with the outside world.
translateResult :: Functor f => f LMachineResult -> f (Plain Term)
translateResult = fmap $ \(Closure t _, _) -> t

-- | Evaluate a term using the L machine.
evaluateL :: Term TyName Name () -> Either LEvaluationException (Term TyName Name ())
evaluateL = translateResult . internalEvaluateL

-- | Evaluate a term using the L machine. May throw an 'LMachineException'.
unsafeEvaluateL :: Term TyName Name () -> EvaluationResultDef
unsafeEvaluateL = either throw id . extractEvaluationResult . evaluateL
