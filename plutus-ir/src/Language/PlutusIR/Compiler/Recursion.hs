{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling PIR recursive let-bound functions into PLC.
module Language.PlutusIR.Compiler.Recursion where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Error
import {-# SOURCE #-} Language.PlutusIR.Compiler.Term
import           Language.PlutusIR.Compiler.Types

import           Control.Monad
import           Control.Monad.Except

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
compileRecTerms :: Compiling m => PLC.Term TyName Name () -> [TermDef TyName Name ()] -> m (PLC.Term TyName Name ())
compileRecTerms body bs = PLC.Apply () <$> mkTupleBinder body (fmap PLC.defVar bs) <*> mkFixpoint bs

-- | Given a list of var decls, create a tuples of values that computes their mutually recursive fixpoint.
mkFixpoint :: Compiling m => [TermDef TyName Name ()] -> m (PLC.Term TyName Name ())
mkFixpoint bs = do
    let tys = fmap (PLC.varDeclType . PLC.defVar) bs
    -- The pairs of types we'll need for fixN
    asbs <- forM tys $ \case
        PLC.TyFun () i o -> pure (i, o)
        _ -> throwError $ CompilationError "Recursive values must be of function type. You may need to manually add unit arguments."

    q <- liftQuote $ freshTyName () "Q"
    choose <- liftQuote $ freshName () "choose"
    let chooseTy = PLC.mkIterTyFun tys (PLC.TyVar () q)

    -- \f1 ... fn -> choose b1 ... bn
    bsLam <- do
          rhss <- traverse (compileTerm . PLC.defVal) bs
          let chosen =  PLC.mkIterApp (PLC.Var () choose) rhss
              abstracted = PLC.mkIterLamAbs (fmap PLC.defVar bs) chosen
          pure abstracted

    -- abstract out Q and choose
    let cLam = PLC.TyAbs () q (PLC.Type ()) $ PLC.LamAbs () choose chooseTy bsLam

    -- fixN {A1 B1 ... An Bn}
    instantiatedFix <- do
        fixN <- liftQuote $ Function.getBuiltinFixN (length bs)
        pure $ PLC.mkIterInst fixN $ foldMap (\(a, b) -> [a, b]) asbs

    pure $ PLC.Apply () instantiatedFix cLam

-- TODO: move to MkPlc?
-- | Given a term, and a list of var decls, creates a function which takes a tuple of values for each decl, and binds
-- them in the body.
mkTupleBinder :: MonadQuote m => PLC.Term TyName Name () -> [VarDecl TyName Name ()] -> m (PLC.Term TyName Name ())
mkTupleBinder body vars = do
    let tys = fmap PLC.varDeclType vars

    tupleTy <- do
        ntuple <- Tuple.getBuiltinTuple (length tys)
        pure $ PLC.mkIterTyApp ntuple tys

    tupleArg <- liftQuote $ freshName () "tuple"

    -- _i tuple
    accesses <- forM [0..(length tys -1)] $ \i -> do
            naccessor <- Tuple.getBuiltinTupleAccessor (length tys) i
            let accessor = PLC.mkIterInst naccessor tys
            pure $ PLC.Apply () accessor (PLC.Var () tupleArg)
    let defsAndAccesses = zipWith PLC.Def vars accesses

    -- let
    --   f_1 = _1 tuple
    --   ..
    --   f_i = _i tuple
    -- in
    --   result
    let finalBound = foldr (\def acc -> PLC.mkTermLet def acc) body defsAndAccesses

    -- \tuple -> finalBound
    pure $ PLC.LamAbs () tupleArg tupleTy finalBound
