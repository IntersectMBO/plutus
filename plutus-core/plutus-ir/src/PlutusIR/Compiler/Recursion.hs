-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Functions for compiling PIR recursive let-bound functions into PLC.
module PlutusIR.Compiler.Recursion where

import PlutusIR
import PlutusIR.Compiler.Definitions
import PlutusIR.Compiler.Provenance
import PlutusIR.Compiler.Types
import PlutusIR.Error
import PlutusIR.MkPir qualified as PIR

import Control.Lens (view)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans

import Data.List.NonEmpty hiding (length)
import Data.Set qualified as Set

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusCore.MkPlc qualified as PLC
import PlutusCore.Quote
import PlutusCore.StdLib.Data.Function qualified as Function
import PlutusCore.StdLib.Meta.Data.Tuple qualified as Tuple

{- Note [Recursive lets]
We need to define these with a fixpoint. We can derive a fixpoint operator for values
already.

However, we also need to work out how to encode recursion over multiple values simultaneously.
The answer is simple - we pass them through as a tuple.

Overall, the translation looks like this. We convert this:

let rec
  f_1 : t_1 = b_1
  ..
  f_i : t_i = b_i
in
  result

into this:

(\tuple : forall r . (t_1 -> .. -> t_i -> r) -> r .
  let
    f_1 = _1 tuple
    ..
    f_i = _i tuple
  in
    result
)
($fixN i$ (\choose f_1 ... f_i . choose b_1 ... b_i))

where _i is the accessor for the ith component of a tuple.

This scheme is a little complicated - why don't we just pass a function directly to the
fixed tuple that consumes the values? Why do the second round of let-binding?

The answer is that in order to use the tuple we have to provide a result type. If we used
it directly, we would have to provide the type of the *result* term, which we may not know.
Here we merely have to provide it with the types of the f_is, which we *do* know.
-}

-- See Note [Recursive lets]
-- | Compile a mutually recursive list of var decls bound in a body.
compileRecTerms
  :: Compiling m uni fun a
  => PIRTerm uni fun a
  -> NonEmpty (TermDef TyName Name uni fun (Provenance a))
  -> DefT SharedName uni fun (Provenance a) m (PIRTerm uni fun a)
compileRecTerms body bs = do
  p <- lift getEnclosing
  fixpoint <- mkFixpoint bs
  Tuple.bindTuple p (PIR._varDeclName . PIR.defVar <$> toList bs) fixpoint body

-- | Given a list of var decls, create a tuples of values that computes their mutually recursive fixpoint.
mkFixpoint
  :: forall m uni fun a
   . Compiling m uni fun a
  => NonEmpty (TermDef TyName Name uni fun (Provenance a))
  -> DefT SharedName uni fun (Provenance a) m (Tuple.Tuple (Term TyName Name uni fun) uni (Provenance a))
mkFixpoint bs = do
  p0 <- lift getEnclosing

  funs <- forM bs $ \(PIR.Def (PIR.VarDecl p name ty) term) ->
    case PIR.mkFunctionDef p name ty term of
      Just fun -> pure fun
      Nothing -> lift $ throwError $ CompilationError (PLC.typeAnn ty) "Recursive values must be of function type"

  inlineFix <- view (ccOpts . coInlineConstants)

  -- See Note [Extra definitions while compiling let-bindings]
  let
    arity = fromIntegral $ length funs
    fixByKey = FixBy
    fixNKey = FixpointCombinator arity
    ann = if inlineFix then annAlwaysInline else annMayInline

  let mkFixByDef = do
        name <- liftQuote $ toProgramName fixByKey
        let (fixByTerm, fixByType) = Function.fixByAndType
        pure (PLC.Def (PLC.VarDecl ann name (noProvenance <$ fixByType)) (noProvenance <$ fixByTerm, Strict), mempty)

  let mkFixNDef = do
        name <- liftQuote $ toProgramName fixNKey
        ((fixNTerm, fixNType), fixNDeps) <-
          if arity == 1
            then pure (Function.fixAndType, mempty)
            -- fixN depends on fixBy
            else do
              fixBy <- lookupOrDefineTerm fixByKey mkFixByDef
              pure (Function.fixNAndType arity (void fixBy), Set.singleton fixByKey)
        pure (PLC.Def (PLC.VarDecl ann name (noProvenance <$ fixNType)) (noProvenance <$ fixNTerm, Strict), fixNDeps)
  fixN <- lookupOrDefineTerm fixNKey mkFixNDef

  liftQuote $ case funs of
    -- Takes a list of function defs and function bodies and turns them into a Scott-encoded tuple, which
    -- happens to be exactly what we want
    f :| [] -> Tuple.getSpineToTuple p0 [(PLC.functionDefToType f, Function.getSingleFixOf p0 fixN f)]
    f :| fs -> Function.getMutualFixOf p0 fixN (f : fs)
