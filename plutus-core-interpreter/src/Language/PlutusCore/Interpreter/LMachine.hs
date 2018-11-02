-- | The L machine
-- A lazy machine based on the L machine of Friedman et al. [Improving the Lazy Krivine Machine]
-- More documentation to follow

-- DON'T LOOK AT THIS - it's horrible!

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

----------------------------------------------------------------------------------------------------

nameStr :: Name () -> String
nameStr n = show $ nameString n

tnameStr :: TyName () -> String
tnameStr n = nameStr $ unTyName n

builtinStr :: TypeBuiltin -> String
builtinStr TyByteString = "bs"
builtinStr TyInteger    = "int"
builtinStr TySize       = "size"


typeStr :: Type TyName () -> String
typeStr (TyVar _ tname)         = tnameStr tname
typeStr (TyFun _ ty1 ty2)       = "(" ++ typeStr ty1 ++ " ~> " ++ typeStr ty2 ++ ")"
typeStr (TyFix _ tname ty)      = "fix " ++ tnameStr tname ++ ".(" ++ typeStr ty ++ ")"
typeStr (TyForall _ tname k ty) = "forall " ++ tnameStr tname ++ ".(" ++ typeStr ty ++ ")"
typeStr (TyBuiltin _ tbi)       = builtinStr tbi
typeStr (TyInt _ n)             = show n
typeStr (TyLam _ tname k ty)    = "TLam " ++ tnameStr tname ++ " (" ++ typeStr ty ++ ")"
typeStr (TyApp _ t1 t2)         = typeStr t1 ++ "<" ++ typeStr t2 ++ ">"




termStr :: Plain Term -> String
termStr (Var _ name)                = nameStr name
termStr (TyAbs _ tyname  k term)    = "TyAbs " ++ tnameStr tyname ++ ".<" ++ termStr term ++ ">"
termStr (LamAbs _ name tyname term) = "Lam " ++ nameStr name ++ " (" ++ termStr term ++ ")"
termStr (Apply _ term1 term2)       = "Apply [" ++ termStr term1 ++ ", " ++ termStr term2 ++ "]"
termStr (Constant _ c)              = "Const " ++ show c
termStr (TyInst _ term ty)          = "TyInst {" ++ termStr term ++ ", " ++ typeStr ty  ++ "}"
termStr (Unwrap _ term)             = "Unwrap (" ++ termStr term  ++ ")"
termStr (Wrap  _ tyname ty term)    = "Wrap (" ++ termStr term ++ ")"
termStr (Error _ _)                 = "Error"

termStr2 :: Plain Term -> String
termStr2 (LamAbs _ name _ _) = "LamAbs " ++ nameStr name
termStr2 t                   = termStr t

trace2 _ y = y
-- trace2 = trace
----------------------------------------------------------------------------------------------------

data LocalResult
    = Success (Plain Term) Heap
    | Failure

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
    in trace2 ("Inserting at " ++ show top') $ (top', Heap (IntMap.insert top' (Unevaluated cl) h) top')

modifyHeap :: Loc -> HeapEntry -> Heap -> Heap
modifyHeap l cl (Heap h top) =
    Heap (IntMap.insert l cl h) top

lookupHeap :: Loc -> Heap -> HeapEntry
lookupHeap l (Heap h _) =
    case IntMap.lookup l h of
      Nothing -> error $ "Missing heap location in lookupHeap: " ++ show l
      Just e  -> e

computeL :: Heap -> Environment -> EvaluationContext -> Plain Term -> LocalResult
computeL heap env ctx (TyInst _ fun ty)      = trace2 ("-> TyInst "  ++ typeStr ty) $
                                               computeL heap env (FrameTyInstArg ty : ctx) fun      -- fun isn't necesaarily a function
computeL heap env ctx (Apply _ fun arg)      = trace2 ("-> Apply " ++ termStr fun ++ " " ++ termStr arg) $
                                               computeL heap env (FrameDelayedArg arg env: ctx) fun
computeL heap env ctx (Wrap ann tyn ty term) = trace2 ("-> Wrap " ++ termStr term) $
                                               computeL heap env (FrameWrap ann tyn ty : ctx) term
computeL heap env ctx (Unwrap _ term)        = trace2 ("-> Unwrap " ++ termStr term) $
                                               computeL heap env (FrameUnwrap : ctx) term
computeL heap env ctx tyAbs@TyAbs{}          = trace2 ("<- tyAbs") $
                                               returnL heap env ctx tyAbs
computeL heap env ctx lamAbs@LamAbs{}        = trace2 ("<- " ++ termStr2 lamAbs) $
                                               returnL heap env ctx lamAbs
computeL heap env ctx constant@Constant{}    = trace2 ("<- Constant " ++ termStr constant) $
                                               returnL heap env ctx constant
computeL _ _   _   Error{}                   = Failure
computeL heap env ctx var@(Var _ name)       = let l = lookupLoc name env
                                               in case lookupHeap l heap of
                                                    Evaluated v -> trace2 ("<- Evaluated " ++ show l ++ ": "
                                                                          ++ termStr v) $ returnL heap env ctx v
                                                    Unevaluated (Closure term env') ->
                                                        trace2 ("-> Unevaluated " ++ show l ++ ": " ++ show term) $
--                                                      trace2 ("env: " ++ show env') $
                                                        computeL heap env' (FrameMark env l: ctx) term -- CHECK THE ENVS
                                                        -- reduce the entry to a value, leaving a mark on
                                                        -- the stack so we know when we've finished
returnL :: Heap -> Environment -> EvaluationContext -> Plain Value -> LocalResult
returnL heap _ []                                 res = Success res heap
returnL heap env (FrameTyInstArg ty        : ctx) fun = instantiateEvaluate heap env ctx ty fun
returnL heap env (FrameDelayedArg arg env' : ctx) val = evaluateFun heap ctx val env arg env'
returnL heap env (FrameWrap ann tyn ty     : ctx) val = returnL heap env ctx $ Wrap ann tyn ty val
returnL heap env (FrameUnwrap              : ctx) dat = case dat of
    Wrap _ _ _ term -> returnL heap env ctx term
    term            -> throw $ MachineException NonWrapUnwrappedMachineError term
returnL (heap@(Heap _ sz)) env (FrameMark env' l: ctx) val =
    trace2 ("<- Mark " ++ show l ++ ", heap size = " ++ show sz) $
           let heap' = modifyHeap l (Evaluated val) heap
           in returnL heap' env' ctx val -- Restore the old environment

-- | Apply a function to an argument and proceed.
-- If the function is a 'LamAbs', then extend the current environment with a new variable and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.

evaluateFun :: Heap -> EvaluationContext -> Plain Term -> Environment -> Plain Term -> Environment -> LocalResult
evaluateFun heap ctx (LamAbs _ var _ body) funEnv arg argEnv =
    let (l, heap') = insertInHeap (Closure arg argEnv) heap
        env9 = updateEnvironment (unUnique $ nameUnique var) l funEnv -- ???
    in computeL heap' env9 ctx body
evaluateFun heap ctx fun funEnv arg argEnv =
-- We have to force the arguments, which means that we need to get the new heap back as well. ****************
   case computeL heap argEnv [] arg of
     Failure -> Failure
     Success arg' heap' ->
         let term = Apply () fun arg'
         in case termAsPrimIterApp term of
              Nothing ->
                  throw $ MachineException NonPrimitiveApplicationMachineError term
                  -- "Cannot reduce a not immediately reducible application."
              Just (IterApp headName spine) ->
                  case runQuote $ applyBuiltinName headName spine of
                    ConstAppSuccess term' -> trace2 ("Evaluated builtin " ++ (show headName)) $ returnL heap' funEnv ctx term'
                    ConstAppStuck         -> returnL heap' funEnv ctx term
                    ConstAppFailure       -> error $ "ConstAppFailure" ++ show term
                    ConstAppError err     -> throw $ MachineException (ConstAppMachineError err) term


-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate
    :: Heap -> Environment -> EvaluationContext -> Type TyName () -> Plain Term -> LocalResult
instantiateEvaluate heap env ctx _  (TyAbs _ _ _ body) = computeL heap env ctx body
instantiateEvaluate heap env ctx ty fun
    | isJust $ termAsPrimIterApp fun = returnL heap env ctx $ TyInst () fun ty
    | otherwise                      = throw $ MachineException NonPrimitiveInstantiationMachineError fun

-- | Evaluate a term using the CEK machine. May throw a 'MachineException'.
evaluateL :: Term TyName Name () -> LocalResult
evaluateL = computeL emptyHeap (Environment IntMap.empty) []

-- | Run a program using the CEK machine. May throw a 'MachineException'.
-- Calls 'evaluateL' under the hood, so the same caveats apply.
runL :: Program TyName Name () -> EvaluationResult
runL (Program _ _ term) =
    case evaluateL term of
      Success r heap -> EvaluationSuccess r
      Failure        -> EvaluationFailure
