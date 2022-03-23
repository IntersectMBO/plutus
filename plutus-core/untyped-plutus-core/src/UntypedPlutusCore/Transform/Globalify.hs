{-# LANGUAGE TupleSections   #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE TypeFamilies #-}
module UntypedPlutusCore.Transform.Globalify (globalifyProgram, globalifyTerm) where

import           Control.Monad.Reader
import Data.Bifunctor
import  PlutusCore.DeBruijn
import           UntypedPlutusCore.Core.Plated
import           UntypedPlutusCore.Core.Type

{- Note [Globalifying]
It's a bit awkward to deal with global variables. Initially, I tried to match on things of the shape

    [ (lam n body) rhs ]

i.e. things that look like a compiled let-binding. But this is not sufficient, because we generate code like
this from datatype bindings:

    [ [ [ (lam n1 (lam n2 (lam n3 body) ) ) rhs3 ] rhs2 ] rhs1]

Furthermore, scripts as we see them before evaluation will be applied to some number of arguments!

I spent a while trying to figure out how to identify the stuff that we wanted as globals, and then I thought
of a different way of thinking of it.

> Look for lambdas which are only ever called once

If you spot a lambda like this, you can safely write its variable binding into a global location, since it
will only ever be assigned to once, and we don't have to worry about escape analysis etc. Conveniently, this
is exactly what all of our compiled let-bindings look like.

How do we spot such a thing? Simple: the only things which can get evaluated multiple times are things that
actually get bound to a variable, i.e. things which appear on the RHS of an application. So we can just recurse
down the tree, ignoring stuff on the RHS of an application.

In terms of implementation, we can also handle this neatly with a new kind of name ('GName') which is either
a normal name of a global name. Mostly "global" lambdas are just like normal lambdas, otherwise.
-}

globalifyProgram :: Program DeBruijn uni fun ann -> (Program DeBruijn uni fun ann, Index)
globalifyProgram (Program x v t) = first (Program x v) $ globalifyTerm t

globalifyTerm :: Term DeBruijn uni fun ann -> (Term DeBruijn uni fun ann, Index)
globalifyTerm t = flip runReader 0 $ gatherGlobals t

-- maxGlobal :: Term (GName name) uni fun a -> Int
-- maxGlobal t = getMax $ foldMapOf (cosmosOf termSubterms) (\case {LamAbs _ (GName w) _  -> Max w; _ -> Max 0}) t

gatherGlobals :: forall m uni fun ann . (m ~ Reader Index) => Term DeBruijn uni fun ann -> m (Term DeBruijn uni fun ann, Index)
-- See Note [Globalifying]
-- This is the key part!
gatherGlobals (Apply x l r) = do
    (l',c) <- gatherGlobals l
    r' <- withReader (,0) (rewriteGlobals r)
    pure (Apply x l' r', c)
gatherGlobals (LamAbs x _n b) = do
    g <- ask
    (b',mx) <- local (+1) $ gatherGlobals b
    pure $ (LamAbs x (DeBruijn (negate g)) b', mx)
gatherGlobals (Delay x b) = first (Delay x) <$> gatherGlobals b
gatherGlobals (Force x b) = first (Force x) <$> gatherGlobals b
gatherGlobals (Var ann (DeBruijn n)) = do
    c <- ask
    pure $ (Var ann $ DeBruijn $ n-c, c)
-- This is just the non-recursive bits
gatherGlobals t = asks (t,)

rewriteGlobals :: Term DeBruijn uni fun ann -> Reader (Index,Index)  (Term DeBruijn uni fun ann)
rewriteGlobals (Var ann (DeBruijn n)) = do
    (g,l) <- ask
    pure $ Var ann $ DeBruijn $
        if n <= l
        then n
        else n-g-l

rewriteGlobals (LamAbs ann _n b) = LamAbs ann (DeBruijn 1) <$> local (second (+1)) (rewriteGlobals b)
rewriteGlobals t = termSubterms rewriteGlobals t
