{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.CkMachine
    ( CkError(..)
    , CkException(..)
    , CkEvalResult(..)
    , evaluateCk
    , runCk
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Constant.Prelude
import           Language.PlutusCore.Constant.View
import           Language.PlutusCore.Constant.Apply

infix 4 |>, <|

data Frame
    = FrameApplyFun (Value TyName Name ())       -- ^ @[V _]@
    | FrameApplyArg (Term TyName Name ())        -- ^ @[_ N]@
    | FrameTyInstArg (Type TyName ())            -- ^ @{_ A}@
    | FrameUnwrap                                -- ^ @(unwrap _)@
    | FrameWrap () (TyName ()) (Type TyName ())  -- ^ @(wrap α A _)@

type Context = [Frame]

data CkError
    = NonPrimitiveInstantiationCkError
      -- ^ An attempt to reduce a not immediately reducible type instantiation.
    | NonWrapUnwrappedCkError
      -- ^ An attempt to unwrap a not wrapped term.
    | NonPrimitiveApplicationCkError
      -- ^ An attempt to reduce a not immediately reducible application.
    | OpenTermEvaluatedCkError
      -- ^ An attempt to evaluate an open term.
    | ConstAppCkError ConstAppError
      -- ^ An attempt to compute a constant application resulted in 'ConstAppError'.

-- | The type of exceptions the CK machine can throw.
data CkException = CkException
    { _ckExceptionError :: CkError              -- ^ An error.
    , _ckExceptionCause :: Term TyName Name ()  -- ^ A 'Term' that caused the error.
    }

-- | The type of results the CK machine returns.
data CkEvalResult
    = CkEvalSuccess (Value TyName Name ())
    | CkEvalFailure
    deriving (Show, Eq)

instance Pretty CkEvalResult where
    pretty (CkEvalSuccess value) = pretty value
    pretty CkEvalFailure         = "Failure"

-- TODO: do we really need all those parens?
constAppErrorString :: ConstAppError -> String
constAppErrorString (SizeMismatchConstAppError seenSize arg) = concat
    [ "encoutered an unexpected size in ("
    , prettyString arg
    , ") (previously seen size: "
    , prettyString seenSize
    , ") in"
    ]
constAppErrorString (IllTypedConstAppError expType constant) = concat
    [ "encountered an ill-typed argument: ("
    , prettyString constant
    , ") (expected type: "
    , prettyString expType
    , ") in"
    ]
constAppErrorString (ExcessArgumentsConstAppError excessArgs) = concat
    [ "attempted to evaluate a constant applied to too many arguments (excess ones are: "
    , prettyString excessArgs
    , ") in"
    ]
constAppErrorString (SizedNonConstantConstAppError arg)       = concat
    [ "encountered a non-constant argument of a sized type: ("
    , prettyString arg
    , ") in"
    ]

ckErrorString :: CkError -> String
ckErrorString NonPrimitiveInstantiationCkError =
    "attempted to reduce a not immediately reducible type instantiation: "
ckErrorString NonWrapUnwrappedCkError          =
    "attempted to unwrap a not wrapped term: "
ckErrorString NonPrimitiveApplicationCkError   =
    "attempted to reduce a not immediately reducible application: "
ckErrorString OpenTermEvaluatedCkError         =
    "attempted to evaluate an open term: "
ckErrorString (ConstAppCkError constAppError)  =
    constAppErrorString constAppError

instance Show CkException where
    show (CkException err cause) = concat
        ["The CK machine " , ckErrorString err, prettyString cause]

instance Exception CkException

-- | Substitute a 'Value' for a variable in a 'Term' that can contain duplicate binders.
-- Do not descend under binders that bind the same variable as the one we're substituting for.
substituteDb
    :: Eq (name a) => name a -> Value tyname name a -> Term tyname name a -> Term tyname name a
substituteDb varFor new = go where
    go (Var ann var)            = if var == varFor then new else Var ann var
    go (TyAbs ann tyn ty body)  = TyAbs ann tyn ty (go body)
    go (LamAbs ann var ty body) = LamAbs ann var ty (goUnder var body)
    go (Apply ann fun arg)      = Apply ann (go fun) (go arg)
    go (Fix ann var ty body)    = Fix ann var ty (goUnder var body)
    go (Constant ann constant)  = Constant ann constant
    go (TyInst ann fun arg)     = TyInst ann (go fun) arg
    go (Unwrap ann term)        = Unwrap ann (go term)
    go (Wrap ann tyn ty term)   = Wrap ann tyn ty (go term)
    go (Error ann ty)           = Error ann ty

    goUnder var term = if var == varFor then term else go term

-- | The computing part of the CK machine. Rules are as follows:
--
-- > s ▷ {M A}      ↦ s , {_ A} ▷ M
-- > s ▷ [M N]      ↦ s , [_ N] ▷ M
-- > s ▷ wrap α A M ↦ s , (wrap α S _) ▷ M
-- > s ▷ unwrap M   ↦ s , (unwrap _) ▷ M
-- > s ▷ abs α K M  ↦ s ◁ abs α K M
-- > s ▷ lam x A M  ↦ s ◁ lam x A M
-- > s ▷ con cn     ↦ s ◁ con cn
-- > s ▷ error A    ↦ ◆
(|>) :: Context -> Term TyName Name () -> CkEvalResult
stack |> TyInst _ fun ty      = FrameTyInstArg ty : stack |> fun
stack |> Apply _ fun arg      = FrameApplyArg arg : stack |> fun
stack |> Wrap ann tyn ty term = FrameWrap ann tyn ty : stack |> term
stack |> Unwrap _ term        = FrameUnwrap : stack |> term
stack |> tyAbs@TyAbs{}        = stack <| tyAbs
stack |> lamAbs@LamAbs{}      = stack <| lamAbs
stack |> constant@Constant{}  = stack <| constant
_     |> Error{}              = CkEvalFailure
_     |> Fix{}                = error "Deprecated."
_     |> var@Var{}            = throw $ CkException OpenTermEvaluatedCkError var

-- | The returning part of the CK machine. Rules are as follows:
--
-- > s , {_ A}           ◁ abs α K M  ↦ s ▷ M
-- > s , [_ N]           ◁ V          ↦ s , [V _] ▷ N
-- > s , [(lam x A M) _] ◁ V          ↦ s ▷ [V/x]M
-- > s , {_ A}           ◁ F          ↦ s ◁ {F A}  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s ◁ [F V]  -- Partially saturated constant.
-- > s , [F _]           ◁ V          ↦ s ◁ W      -- Fully saturated constant, [F V] ~> W.
-- > s , (wrap α S _)    ◁ V          ↦ s ◁ wrap α S V
-- > s , (unwrap _)      ◁ wrap α A V ↦ s ◁ V
(<|) :: Context -> Value TyName Name () -> CkEvalResult
[]                           <| term      = CkEvalSuccess term
FrameTyInstArg ty    : stack <| fun       = instantiateEvaluate stack ty fun
FrameApplyArg arg    : stack <| fun       = FrameApplyFun fun : stack |> arg
FrameApplyFun fun    : stack <| arg       = applyEvaluate stack fun arg
FrameWrap ann tyn ty : stack <| value     = stack <| Wrap ann tyn ty value
FrameUnwrap          : stack <| wrapped   = case wrapped of
    Wrap _ _ _ term -> stack <| term
    term            -> throw $ CkException NonWrapUnwrappedCkError term

-- | Instantiate a term with a type and proceed.
-- In case of 'TyAbs' just ignore the type. Otherwise check if the term is an
-- iterated application of a 'BuiltinName' to a list of 'Value's and, if succesful,
-- apply the term to the type via 'TyInst'.
instantiateEvaluate :: Context -> Type TyName () -> Term TyName Name () -> CkEvalResult
instantiateEvaluate stack _  (TyAbs _ _ _ body) = stack |> body
instantiateEvaluate stack ty fun
    | isJust $ termAsPrimIterApp fun = stack <| TyInst () fun ty
    | otherwise                      =
          throw $ CkException NonPrimitiveInstantiationCkError fun

-- | Apply a function to an argument and proceed.
-- If the function is not a 'LamAbs', then 'Apply' it to the argument and view this
-- as an iterated application of a 'BuiltinName' to a list of 'Value's.
-- If succesful, proceed with either this same term or with the result of the computation
-- depending on whether 'BuiltinName' is saturated or not.
applyEvaluate :: Context -> Value TyName Name () -> Value TyName Name () -> CkEvalResult
applyEvaluate stack (LamAbs _ name _ body) arg = stack |> substituteDb name arg body
applyEvaluate stack fun                    arg =
    let term = Apply () fun arg in
        case termAsPrimIterApp term of
            Nothing                       ->
                throw $ CkException NonPrimitiveApplicationCkError term
            Just (IterApp headName spine) ->
                case applyBuiltinName headName spine of
                    ConstAppSuccess term' -> stack <| term'
                    ConstAppFailure       -> CkEvalFailure
                    ConstAppStuck         -> stack <| term
                    ConstAppError err     ->
                        throw $ CkException (ConstAppCkError err) term

-- | Evaluate a term using the CK machine. May throw a 'CkException'.
-- This differs from the spec version: we do not have the following rule:
--
-- > s , {_ A} ◁ F ↦ s ◁ W  -- Fully saturated constant, {F A} ~> W.
--
-- The reason for that is that the operational semantics of constant applications is
-- unaffected by types as it supports full type erasure, hence @{F A}@ can never compute
-- if @F@ does not compute, so we simply do not introduce a rule that can't possibly fire.
evaluateCk :: Term TyName Name () -> CkEvalResult
evaluateCk = ([] |>)

-- | Run a program using the CK machine. May throw a 'CkException'.
-- Calls 'evaluateCk' under the hood, so the same caveats apply.
runCk :: Program TyName Name () -> CkEvalResult
runCk (Program _ _ term) = evaluateCk term
