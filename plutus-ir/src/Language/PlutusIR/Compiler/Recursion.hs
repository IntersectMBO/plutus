{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling PIR recursive let-bound functions into PLC.
module Language.PlutusIR.Compiler.Recursion where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Error
import           Language.PlutusIR.Compiler.Names
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
    fixpoint <- mkFixpoint bs
    Tuple.bindTuple p (PLC.varDeclName . PLC.defVar <$> bs) fixpoint body

-- | Given a list of var decls, create a tuples of values that computes their mutually recursive fixpoint.
mkFixpoint :: Compiling m e a => [TermDef TyName Name (Provenance a)] -> m (Tuple.Tuple (Provenance a))
mkFixpoint bs = do
    p0 <- ask

    funs <- forM bs $ \(PLC.Def (PLC.VarDecl p name ty) term) -> case ty of
        PLC.TyFun _ i o -> Function.Function p i o . PLC.Def name <$> compileTerm term
        _ -> throwing _Error $ CompilationError (PLC.tyLoc ty) "Recursive values must be of function type. You may need to manually add unit arguments."

    liftQuote $ Function.getBuiltinMutualFixOf p0 funs
