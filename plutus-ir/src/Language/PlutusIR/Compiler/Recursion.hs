{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling PIR recursive let-bound functions into PLC.
module Language.PlutusIR.Compiler.Recursion where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Provenance
import {-# SOURCE #-} Language.PlutusIR.Compiler.Term
import           Language.PlutusIR.Compiler.Types

import           Control.Monad
import           Control.Monad.Error.Lens
import           Control.Monad.Reader

import qualified Language.PlutusCore                        as PLC
import qualified Language.PlutusCore.MkPlc                  as PLC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Function   as Function
import qualified Language.PlutusCore.StdLib.Meta.Data.Tuple as Tuple

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

 -- See note [Recursive lets]
-- | Compile a mutually recursive list of var decls bound in a body.
compileRecTerms :: Compiling m e a => PLCTerm a -> [TermDef TyName Name (Provenance a)] -> m (PLCTerm a)
compileRecTerms body bs = do
    p <- ask
    PLC.Apply p <$> mkTupleBinder body (fmap PLC.defVar bs) <*> mkFixpoint bs

-- | Given a list of var decls, create a tuples of values that computes their mutually recursive fixpoint.
mkFixpoint :: Compiling m e a => [TermDef TyName Name (Provenance a)] -> m (PLCTerm a)
mkFixpoint bs = do
    p <- ask

    let tys = fmap (PLC.varDeclType . PLC.defVar) bs
    -- The pairs of types we'll need for fixN
    asbs <- forM tys $ \case
        PLC.TyFun _ i o -> pure (i, o)
        t -> throwing _Error $ CompilationError (PLC.tyLoc t) "Recursive values must be of function type. You may need to manually add unit arguments."

    q <- liftQuote $ freshTyName p "Q"
    choose <- liftQuote $ freshName p "choose"
    let chooseTy = PLC.mkIterTyFun p tys (PLC.TyVar p q)

    -- \f1 ... fn -> choose b1 ... bn
    bsLam <- do
          rhss <- traverse (compileTerm . PLC.defVal) bs
          let chosen =  PLC.mkIterApp p (PLC.Var p choose) rhss
              abstracted = PLC.mkIterLamAbs p (fmap PLC.defVar bs) chosen
          pure abstracted

    -- abstract out Q and choose
    let cLam = PLC.TyAbs p q (PLC.Type p) $ PLC.LamAbs p choose chooseTy bsLam

    -- fixN {A1 B1 ... An Bn}
    instantiatedFix <- do
        fixN <- setProvenance p <$> (liftQuote $ Function.getBuiltinFixN (length bs))
        pure $ PLC.mkIterInst p fixN $ foldMap (\(a, b) -> [a, b]) asbs

    pure $ PLC.Apply p instantiatedFix cLam

-- TODO: move to MkPlc?
-- | Given a term, and a list of var decls, creates a function which takes a tuple of values for each decl, and binds
-- them in the body.
mkTupleBinder :: Compiling m e a => PLCTerm a -> [VarDecl TyName Name (Provenance a)] -> m (PLCTerm a)
mkTupleBinder body vars = do
    p <- ask

    let tys = fmap PLC.varDeclType vars

    tupleTy <- do
        ntuple <- setProvenance p <$> Tuple.getBuiltinTuple (length tys)
        pure $ PLC.mkIterTyApp p ntuple tys

    tupleArg <- liftQuote $ freshName p "tuple"

    -- _i tuple
    accesses <- forM [0..(length tys -1)] $ \i -> do
            naccessor <- setProvenance p <$> Tuple.getBuiltinTupleAccessor (length tys) i
            let accessor = PLC.mkIterInst p naccessor tys
            pure $ PLC.Apply p accessor (PLC.Var p tupleArg)
    let defsAndAccesses = zipWith PLC.Def vars accesses

    -- let
    --   f_1 = _1 tuple
    --   ..
    --   f_i = _i tuple
    -- in
    --   result
    let finalBound = foldr (\def acc -> PLC.mkTermLet p def acc) body defsAndAccesses

    -- \tuple -> finalBound
    pure $ PLC.LamAbs p tupleArg tupleTy finalBound
