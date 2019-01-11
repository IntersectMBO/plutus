{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Implements a PIR-to-PIR transformation that makes all recursive term definitions
-- compilable to PLC. See Note [Thunking recursions] for details.
module Language.PlutusIR.Transform.ThunkRecursions (thunkRecursionsTerm) where

import           PlutusPrelude

import           Language.PlutusIR
import           Language.PlutusIR.MkPir
import           Language.PlutusIR.Transform.Substitute

import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Unit   as Unit

import           Control.Lens

import           Data.List
import qualified Data.Map                               as Map
import           Data.Traversable

{- Note [Thunking recursions]
Our fixpoint combinators in Plutus Core know how to handle mutually recursive values
of *function type*. That is, we can define `map : List Int -> List Int` but *not*
`map : forall a . List a -> List a`, because the latter has a universally
qualified type, instead of a function type (although it is a function underneath).

We could solve this problem for universally quantified values by lifting the forall
out of the recursion. This is a bit like performing the following transformation:

    map : forall a b . (a -> b) -> List a -> List b
    map f xs = case xs of
        [] -> []
        x:xs -> f x : map f xs

vs

    -- non-recursive
    map : forall a b . (a -> b) -> List a -> List a
    map = map'
        where
            -- recursive, but *monomorphic* in the 'a' and 'b' we instantiate to, so of
            -- simple function type
            map' : (a -> b) -> List a -> List b
            map' f xs = case xs of
                [] -> []
                x:xs -> f x : map' f xs

However, this has two drawbacks:
- It only works for polymorphic functions. There are other kinds of non-function
  values which we might want to define recursively.
- It doesn't work if we use polymorphic recursion, because the function we are
  defining is monomorphic, so the recursive call must be at the same type.

The latter is quite annoying, because in practice all interesting functions over
irregular datatypes will use polymorphic recursion, and we've gone to some lengths
to allow ourselves to define irregular datatypes.

The alternative solution is: given a proposed recursive definition of a value of
non-function type, we simply *make* it into a value of function type, by adding
a unit argument and forcing it at all the uses in the body.

So we do something like this:

    -- non-recursive, acts as an "adaptor" for other consumers of the original function
    map : forall a b . (a -> b) -> List a -> List b
    map = map' () @a
        where
            -- recursive, but thunked, so of simple function type
            map' : () -> forall a' b' . (a' -> b') -> List a' -> List b'
            map' _ f xs = case xs of
                [] -> []
                x:xs -> f x : (map' () @b) f xs

This has the advantage of always working, but it's annoying because we have to go
in and edit the body of the function definition.

The algorithm operates as follows:
- Given a recursive let binding with some bindings that need thunking (i.e. are not of simple function type):
    - For each binding that needs thunking with name `n`, type `t`, and body `b`:
        - Make a new binding with a new name `n'`, type `() -> t` and body `\() -> b`.
        - Add the mapping `n => n' ()` into a substitution map.
        - Make an adaptor binding with name `n`, type `t`, and body `n' ()`.
    - Use the substitution map to replace all occurrences of old names inside the new bindings and any bindings
      that didn't need thunking.
    - The final term is `let rec <new bindings ++ non thunked bindings> in let nonrec <adaptor bindings> in <original body>`.
-}

{- Note [Transformation vs compilation]
We have two options for where we can put this transformation:
- We can do it on-demand during compilation.
- We can do it in advance in a separate pass.

The advantage of the former is that it makes compilation "more total", otherwise
we have to have a case where we give an error if we see a recursive binding we can't
handle, even if we've already run the pass to get rid of them.

(If we were doing a "Trees that Grow" approach we could disable the constructor afterwards,
which would be pretty nice.)

However, the advantage of the second approach is that it keeps it separate and independently
testable, which is handy.

This isn't very clear-cut - since PIR is a superset of PLC, we could implement our compiler
as a set of transformations, each of which eliminates one of the PIR features, until we're only
left with the PLC subset. This would be quite elegant - except that the final "lowering" step
would be quite ugly as it would just have to fail if it saw any PIR features.
-}

isFunctionType :: Type tyname a -> Bool
isFunctionType = \case
    TyFun {} -> True
    _ -> False

needsThunking :: Binding tyname name a -> Bool
needsThunking = \case
    TermBind _ (VarDecl _ _ ty) _ -> not $ isFunctionType ty
    _ -> False

thunkRecursionsBinding :: MonadQuote m => Binding TyName Name a -> m (Binding TyName Name a)
thunkRecursionsBinding = \case
    TermBind x d rhs -> TermBind x d <$> thunkRecursionsTerm rhs
    -- nothing to do for type bindings or datatype bindings
    x -> pure x

thunkRecursionsTerm :: MonadQuote m => Term TyName Name a -> m (Term TyName Name a)
thunkRecursionsTerm = \case
    Let x Rec bs t -> do
        -- See Note [Thunking recursions]

        -- TODO: possibly this should use provenances?
        let generated = x

        t' <- thunkRecursionsTerm t
        bs' <- traverse thunkRecursionsBinding bs

        let (needThunking, okay) = partition needsThunking bs'

        if null needThunking
        then pure $ mkLet x Rec okay t'
        else constructThunkedLet generated okay needThunking t'
    -- boring cases
    Let x NonRec bs t -> Let x NonRec <$> traverse thunkRecursionsBinding bs <*> thunkRecursionsTerm t
    TyAbs x tn k t -> TyAbs x tn k <$> thunkRecursionsTerm t
    LamAbs x n ty t -> LamAbs x n ty <$> thunkRecursionsTerm t
    Apply x t1 t2 -> Apply x <$> thunkRecursionsTerm t1 <*> thunkRecursionsTerm t2
    TyInst x t ty -> TyInst x <$> thunkRecursionsTerm t <*> pure ty
    IWrap x pat arg t -> IWrap x pat arg <$> thunkRecursionsTerm t
    Unwrap x t -> Unwrap x <$> thunkRecursionsTerm t
    t -> pure t

data ThunkedNonTermBinding = ThunkedNonTermBinding
instance Show ThunkedNonTermBinding where
    show _ = "Tried to thunk a non-term binding. This should never happen, please report a bug to the Plutus Team"
instance Exception ThunkedNonTermBinding

-- See Note [Thunking recursions]
constructThunkedLet
    :: (MonadQuote m)
    => a
    -> [Binding TyName Name a]
    -> [Binding TyName Name a]
    -> Term TyName Name a
    -> m (Term TyName Name a)
constructThunkedLet ann okay needThunking body = do
    -- These are all going to be used in a "closed" fashion, so it's fine to reuse them so long
    -- as we rename before typechecking.
    argName <- liftQuote $ freshName ann "arg"
    unit <- const ann <<$>> liftQuote Unit.getBuiltinUnit
    unitval <- const ann <<$>> embedIntoIR <$> liftQuote Unit.getBuiltinUnitval

    {-
    We need several pieces, and it is convenient to construct them simultaneously:
    - A new name for the thunked binding.
    - A substitution mapping from the old name to a forced application of the new name.
    - The new thunked binding (using the new name, and a delayed type).
    - An adaptor binding from the old name to a forced application of the new name, so that
      existing consumers inside the let binding can be left untouched.
    -}
    processed <- for needThunking $ \case
        TermBind x' oldVd@(VarDecl x'' oldName ty) rhs -> do
            newName <- liftQuote $ freshName ann $ nameString oldName <> "_thunked"
            let forcedApp = Apply ann (Var ann newName) unitval
            let substitution = (oldName, forcedApp)
            let thunked = TermBind x' (VarDecl x'' newName (TyFun ann unit ty)) (LamAbs ann argName unit rhs)
            let adaptor = TermBind ann oldVd forcedApp
            pure (substitution, thunked, adaptor)
        -- This case shouldn't happen, since only term bindings will need thunking
        _ -> throw ThunkedNonTermBinding

    let thunkedBindings = processed ^.. traverse . _2
    let newBindings = thunkedBindings ++ okay

    -- Now we have to handle references to the old name. All the references inside the RHSs of the bindings
    -- should be substituted for a forced application of the new name.
    let renamedBindings =
          let substitutionMap = Map.fromList $ processed ^.. traverse . _1
              -- substitution function for names
              nameF n = Map.lookup n substitutionMap
              -- do nothing for type names
              tynameF = const Nothing
          in fmap (substBinding tynameF nameF) newBindings

    let adaptorBindings = processed ^.. traverse . _3

    -- The final term is a recursive let with the thunkified bindings, surrounding an inner let with the adaptors,
    -- and then the body.
    pure $ mkLet ann Rec renamedBindings $ mkLet ann NonRec adaptorBindings body
