{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

{-| A pass that evaluates fully-applied builtin applications in the program.
This functions as a generic constant-folding pass. -}
module UntypedPlutusCore.Transform.EvaluateBuiltins
  ( evaluateBuiltins
  , certifiedBuiltinToFun
  ) where

import PlutusCore.Builtin
import PlutusCore.Default.Builtins (DefaultFun (..))
import UntypedPlutusCore.Core.Plated (termSubterms)
import UntypedPlutusCore.Core.Type
import UntypedPlutusCore.Transform.Certify.Trace qualified as Trace
import UntypedPlutusCore.Transform.Optimizer

import Control.Lens (transformOf)
import Data.Functor (void)
import Universe (Some (..), ValueOf (..))

{-| Application context for UPLC terms. Unlike the PIR @AppContext@, there are
no type applications, so 'Force' takes the place of 'TypeAppContext'. -}
data AppContext name uni fun a
  = TermAppContext (Term name uni fun a) a (AppContext name uni fun a)
  | ForceContext a (AppContext name uni fun a)
  | AppContextEnd

{-| Split a term into its head and the sequence of 'Apply'/'Force' wrappers
surrounding it. This handles 'Force' in addition to 'Apply', unlike the
exported 'splitApplication'. -}
splitBuiltinApplication
  :: Term name uni fun a
  -> (Term name uni fun a, AppContext name uni fun a)
splitBuiltinApplication = go AppContextEnd
  where
    go ctx = \case
      Apply ann fun arg -> go (TermAppContext arg ann ctx) fun
      Force ann t -> go (ForceContext ann ctx) t
      t -> (t, ctx)

{-| Evaluate fully-applied builtin applications.

The @shouldFold@ predicate determines which builtins may be folded; use
'certifiedBuiltins' for the certified subset or @const True@ for all builtins.

The @isSerializableConstant@ predicate guards against introducing constants
that cannot be flat-encoded (e.g. BLS12-381 group elements).
See Note [Unserializable constants] in PlutusIR.Analysis.Builtins. -}
evaluateBuiltins
  :: forall name uni fun m a
   . ( Monad m
     , ToBuiltinMeaning uni fun
     , Typeable name
     )
  => Bool
  -- ^ If 'True', do not fold builtins that emit logs (e.g. @trace@).
  -> BuiltinSemanticsVariant fun
  -> CostingPart uni fun
  -> (fun -> Bool)
  -- ^ Which builtins to fold.
  -> (Some (ValueOf uni) -> Bool)
  {-^ Whether a constant produced by folding is serializable. Return 'False'
  to prevent the fold from introducing an unserializable constant into the
  program (e.g. BLS12-381 group elements). -}
  -> Trace.OptStage
  -> Term name uni fun a
  -> OptimizerT name uni fun a m (Term name uni fun a)
evaluateBuiltins preserveLogging semVar costModel shouldFold isSerializableConstant optStage term = do
  let result = transformOf termSubterms processTerm term
  recordOptimization term optStage result
  pure result
  where
    eval
      :: BuiltinRuntime (Term name uni fun ())
      -> AppContext name uni fun a
      -> Maybe (Term name uni fun ())
    eval (BuiltinCostedResult _ getFXs) AppContextEnd =
      case getFXs of
        BuiltinSuccess y -> Just y
        -- Leave terms that produce logs if we're asked to preserve logging
        -- behaviour (e.g. `trace "hello" x` in certified mode).
        BuiltinSuccessWithLogs _ y -> if preserveLogging then Nothing else Just y
        -- Evaluation failure (e.g. divideInteger 1 0) – leave unchanged.
        BuiltinFailure {} -> Nothing
    eval (BuiltinExpectArgument toRuntime) (TermAppContext arg _ ctx) =
      eval (toRuntime $ void arg) ctx
    eval (BuiltinExpectForce runtime) (ForceContext _ ctx) =
      eval runtime ctx
    -- Argument mismatch (including under-application) – leave unchanged.
    eval _ _ = Nothing

    termIsSerializable :: Term name uni fun () -> Bool
    termIsSerializable = \case
      Constant _ c -> isSerializableConstant c
      Var {} -> True
      Builtin {} -> True
      Error {} -> True
      LamAbs _ _ body -> termIsSerializable body
      Delay _ body -> termIsSerializable body
      Force _ body -> termIsSerializable body
      Apply _ f arg -> termIsSerializable f && termIsSerializable arg
      Constr _ _ args -> all termIsSerializable args
      Case _ scrut alts -> termIsSerializable scrut && all termIsSerializable alts

    processTerm :: Term name uni fun a -> Term name uni fun a
    processTerm t = case splitBuiltinApplication t of
      (Builtin x bn, argCtx)
        | shouldFold bn ->
            let runtime = toBuiltinRuntime costModel (toBuiltinMeaning semVar bn)
             in case eval runtime argCtx of
                  -- Replace all annotations in the result with the annotation of
                  -- the Builtin node (see the analogous note in PIR.EvaluateBuiltins).
                  -- Guard against introducing unserializable constants (e.g. BLS
                  -- group elements); see Note [Unserializable constants].
                  Just t' | termIsSerializable t' -> x <$ t'
                  _ -> t
      _ -> t

{-| Map each 'Trace.CertifiedBuiltin' to its corresponding 'DefaultFun'.
This is the single authoritative mapping between the FFI-linked
'Trace.CertifiedBuiltin' type (shared with the Agda certifier) and
the Haskell 'DefaultFun' enum. -}
certifiedBuiltinToFun :: Trace.CertifiedBuiltin -> DefaultFun
certifiedBuiltinToFun = \case
  Trace.CertAddInteger -> AddInteger
  Trace.CertSubtractInteger -> SubtractInteger
  Trace.CertMultiplyInteger -> MultiplyInteger
  Trace.CertDivideInteger -> DivideInteger
  Trace.CertQuotientInteger -> QuotientInteger
  Trace.CertRemainderInteger -> RemainderInteger
  Trace.CertModInteger -> ModInteger
  Trace.CertEqualsInteger -> EqualsInteger
  Trace.CertLessThanInteger -> LessThanInteger
  Trace.CertLessThanEqualsInteger -> LessThanEqualsInteger
  Trace.CertIfThenElse -> IfThenElse
  Trace.CertChooseUnit -> ChooseUnit
  Trace.CertFstPair -> FstPair
  Trace.CertSndPair -> SndPair
  Trace.CertChooseList -> ChooseList
  Trace.CertMkCons -> MkCons
  Trace.CertHeadList -> HeadList
  Trace.CertTailList -> TailList
  Trace.CertNullList -> NullList
  Trace.CertDropList -> DropList
  Trace.CertChooseData -> ChooseData
  Trace.CertConstrData -> ConstrData
  Trace.CertMapData -> MapData
  Trace.CertListData -> ListData
  Trace.CertIData -> IData
  Trace.CertUnConstrData -> UnConstrData
  Trace.CertUnMapData -> UnMapData
  Trace.CertUnListData -> UnListData
  Trace.CertUnIData -> UnIData
  Trace.CertEqualsData -> EqualsData
  Trace.CertMkPairData -> MkPairData
  Trace.CertMkNilData -> MkNilData
  Trace.CertMkNilPairData -> MkNilPairData
