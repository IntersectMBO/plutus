-- | 'Eq' instances for core data types.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.PlutusCore.Core.Instance.Eq
    ( eqTypeM
    , eqTermM
    , eqProgramM
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core.Type
import           Language.PlutusCore.Eq
import           Language.PlutusCore.Name
import           Language.PlutusCore.Rename.Monad
import           Language.PlutusCore.Universe

-- See Note [Annotations and equality].

instance Eq (Kind ann) where
    Type _                == Type _                = True
    KindArrow _ dom1 cod1 == KindArrow _ dom2 cod2 = dom1 == dom2 && cod1 == cod2
    Type{}      == _ = False
    KindArrow{} == _ = False

instance Eq (Builtin ann) where
    BuiltinName    _ name1 == BuiltinName    _ name2 = name1 == name2
    DynBuiltinName _ name1 == DynBuiltinName _ name2 = name1 == name2
    BuiltinName{}    == _ = False
    DynBuiltinName{} == _ = False

instance Eq (Version ann) where
    Version _ n1 m1 p1 == Version _ n2 m2 p2 = [n1, m1, p1] == [n2, m2, p2]

instance (HasUniques (Type tyname uni ann), GEq uni) => Eq (Type tyname uni ann) where
    ty1 == ty2 = runEqRename @TypeEtaMapping $ eqTypeM ty1 ty2

instance (HasUniques (Term tyname name uni ann), GEq uni, Closed uni, uni `Everywhere` Eq) =>
            Eq (Term tyname name uni ann) where
    term1 == term2 = runEqRename $ eqTermM term1 term2

instance (HasUniques (Program tyname name uni ann), GEq uni, Closed uni, uni `Everywhere` Eq) =>
            Eq (Program tyname name uni ann) where
    prog1 == prog2 = runEqRename $ eqProgramM prog1 prog2

type EqRenameOf ren a = HasUniques a => a -> a -> EqRename ren

{- Note [Eta-equality]
During type checking we may end up performing an equality check of two types that looks like this:

    h f == h (\x -> f x)

In particular, this is likely to happen when type checking functions operating on lambda-encoded
GADTs (like in the @.../Examples/Data/Vec.hs@ file). Such an equality check amounts to checking
that functions from both the sides of the equation are equal (both the functions are @h@, so this
checks succeeds) and checking that arguments are equal as well. I.e.

    f == (\x -> f x)

has to hold. But whether it holds or not depends on whether we support eta-equality for type-level
functions or not (see https://ncatlab.org/nlab/show/eta-conversion).

It might seem that the simplest way of supporting eta-equality is by eta-expanding the side of the
equation that doesn't start with a lambda (the LHS in the example above). That would transform our
example into

    (\x -> f x) == (\x -> f x)

which can be checked with our usual strategy from there on. However, we cannot simply copy the
lambda-binding from the RHS, because the variable that it binds can be referenced (as a free
variable) in @f@ from the LHS, in which case naively prepending a lambda would change the meaning
of the type on the LHS. For example if we have the following equality check

    f x == (\x -> f x x)

then we cannot simply expand the LHS to @\x -> f x x@ by copying the lambda from the RHS as that
would change the meaning of the type.

So what we are forced to do is to invent a fresh variable, lambda-bind it and apply the function
to that variable to transform the original example into

    (\y -> f y) == (\x -> f x)

where @y@ is not referenced in @f@. Checking equality of these two types is still a regular thing.
However, in order to invent a fresh variable we need to be in the 'Quote' monad and we need to know
what free variables both the sides of the equation reference. I.e. we have to perform a prepass on
both the sides before checking their equality. This is a rather big cost to pay for such a simple
feature, especially given the fact that the two sides may start with different type constructors and
we want to return 'False' immediately in that case instead of preprocessing anything fully (we could
try using some meta-circular programming to overcome this inefficiency problem, but that'd be a
terrible overkill).

What we're left with is eta-contracting the side of the equation that starts with a lambda. I.e.
turning the original equation into

    f == f

by eta-contracting @\x -> f x@ (the RHS) into @f@. However, we cannot cut @\x -> f x@ into @f@ and
proceed checking equality without doing anything about @x@. Consider:

    f x == (\x -> f x x)

we can't simply cut @(\x -> f x x)@ into @f x@, because on the LHS we have a type that references
@x@ (a completely different free variable with the same name that we have bound on the LHS). This
is similar to the aforementioned problem where we could not eta-expand @f x@ into @\x -> f x x@.

Hence we need to explicitly record that @x@ is not in scope in @f x@ on the RHS and fail on
encountering it while checking

    f x == f x

after "eta-contracting" @\x -> f x x@ into the wrong @f x@.

But our problems don't end here. Consider the following equation:

    f == (\x x -> f x x)

If we simply cut @\x x -> f x x@ into @\x -> f x@ and record that @x@ must be out of scope in that
type and proceed, then we'll find out that @x@ is indeed out of scope there, because there's a
lambda binding the same variable and thus shadowing the original one. And then we proceed and
eta-contract @\x -> f x@ into @f@. Clearly those two types are very different and the algorithm
does not handle this case correctly.

Note however that we do want to handle shadowing like that when a lambda that binds a variable
shadowing an existing one is not amongst the leading lambdas, i.e. it's either applied in the body
of the n-ary lambda term or an argument there. For example, when performing this equality
check:

    f (\x -> x) == (\x -> f (\x -> x) x)

we do want the first @x@ bound on the RHS to be shadowed by the second one.

What we can do here is remove all the leading lambdas in a single pass and ensure that the
variables they bind are all distinct (as @\x x -> f@ can never be eta-contracted into @f@
regardless of what @f@ is).

This wouldn't be a correct thing to do, if we were to eta-contract both the sides of an equation
first and only then check their equality, because then we wouldn't be able to eta-contract the RHS
of this equality check that is meant to succeed:

    (\x -> f) == (\x x -> f x)

However the case where both the sides start with a lambda is already correctly handled by the main
machinery, so when we do eta-contraction, we can safely assume that the other side of the equation
does not have any leading lambdas.
-}

-- | Eta-contract a type and feed the result to the provided continuation that gets executed in a
-- context extended with all removed lambda-bound variables mapped to 'Nothing' (meaning they are
-- not in scope in the eta-contracted function).
withFullyEtaContracted
    :: ( HasUnique tyname TypeUnique
       , HasMapping (Bilateral ren) (dir TypeUnique) (Maybe TypeUnique)
       )
    => (TypeUnique -> dir TypeUnique)
    -> tyname
    -> Type tyname uni ann
    -> (Type tyname uni ann -> EqRename ren)
    -> EqRename ren
withFullyEtaContracted dir name0 = stripTyLams [name0 ^. unique] where
    stripTyLams uniqs (TyLam _ name _ body') k
        | uniq `elem` uniqs = empty
        | otherwise         = stripTyLams (uniq : uniqs) body' k
        where uniq = name ^. unique
    stripTyLams names body                   k = stripTyApps names body k

    stripTyApps []              fun k = k fun
    stripTyApps (uniq1 : uniqs) fun k = case fun of
        TyApp _ fun' (TyVar _ name2) | uniq1 == name2 ^. unique ->
            withMappedUnique (dir uniq1) Nothing $ stripTyApps uniqs fun' k
        _ -> empty

-- See Note [Modulo alpha].
-- See Note [Scope tracking]
-- See Note [Side tracking]
-- See Note [No catch-all].
-- | Check equality of two 'Type's.
eqTypeM
    :: (HasMapping ren TypeUnique (Maybe TypeUnique), GEq uni)
    => EqRenameOf ren (Type tyname uni ann)
eqTypeM (TyVar _ name1) (TyVar _ name2) =
    eqNameM name1 name2
eqTypeM (TyLam _ name1 kind1 ty1) (TyLam _ name2 kind2 ty2) = do
    eqM kind1 kind2
    withTwinBindings name1 name2 $ eqTypeM ty1 ty2
eqTypeM (TyLam _ name1 _ ty1) f2 =
    withFullyEtaContracted LR name1 ty1 $ \f1 -> eqTypeM f1 f2
eqTypeM f1 (TyLam _ name2 _ ty2) =
    withFullyEtaContracted RL name2 ty2 $ \f2 -> eqTypeM f1 f2
eqTypeM (TyForall _ name1 kind1 ty1) (TyForall _ name2 kind2 ty2) = do
    eqM kind1 kind2
    withTwinBindings name1 name2 $ eqTypeM ty1 ty2
eqTypeM (TyIFix _ pat1 arg1) (TyIFix _ pat2 arg2) = do
    eqTypeM pat1 pat2
    eqTypeM arg1 arg2
eqTypeM (TyApp _ fun1 arg1) (TyApp _ fun2 arg2) = do
    eqTypeM fun1 fun2
    eqTypeM arg1 arg2
eqTypeM (TyFun _ dom1 cod1) (TyFun _ dom2 cod2) = do
    eqTypeM dom1 dom2
    eqTypeM cod1 cod2
eqTypeM (TyBuiltin _ bi1) (TyBuiltin _ bi2) =
    eqM bi1 bi2
eqTypeM TyVar{}     _ = empty
eqTypeM TyForall{}  _ = empty
eqTypeM TyIFix{}    _ = empty
eqTypeM TyApp{}     _ = empty
eqTypeM TyFun{}     _ = empty
eqTypeM TyBuiltin{} _ = empty

-- See Note [Modulo alpha].
-- See Note [Scope tracking]
-- See Note [Side tracking]
-- See Note [No catch-all].
-- | Check equality of two 'Term's.
eqTermM
    :: (GEq uni, Closed uni, uni `Everywhere` Eq)
    => EqRenameOf ScopedEtaMapping (Term tyname name uni ann)
eqTermM (LamAbs _ name1 ty1 body1) (LamAbs _ name2 ty2 body2) = do
    eqTypeM ty1 ty2
    withTwinBindings name1 name2 $ eqTermM body1 body2
eqTermM (TyAbs _ name1 kind1 body1) (TyAbs _ name2 kind2 body2) = do
    eqM kind1 kind2
    withTwinBindings name1 name2 $ eqTermM body1 body2
eqTermM (IWrap _ pat1 arg1 term1) (IWrap _ pat2 arg2 term2) = do
    eqTypeM pat1 pat2
    eqTypeM arg1 arg2
    eqTermM term1 term2
eqTermM (Apply _ fun1 arg1) (Apply _ fun2 arg2) = do
    eqTermM fun1 fun2
    eqTermM arg1 arg2
eqTermM (Unwrap _ term1) (Unwrap _ term2) =
    eqTermM term1 term2
eqTermM (Error _ ty1) (Error _ ty2) =
    eqTypeM ty1 ty2
eqTermM (TyInst _ term1 ty1) (TyInst _ term2 ty2) = do
    eqTermM term1 term2
    eqTypeM ty1 ty2
eqTermM (Var _ name1) (Var _ name2) =
    eqNameM name1 name2
eqTermM (Constant _ con1) (Constant _ con2) =
    eqM con1 con2
eqTermM (Builtin _ bi1) (Builtin _ bi2) =
    eqM bi1 bi2
eqTermM LamAbs{}   _ = empty
eqTermM TyAbs{}    _ = empty
eqTermM IWrap{}    _ = empty
eqTermM Apply{}    _ = empty
eqTermM Unwrap{}   _ = empty
eqTermM Error{}    _ = empty
eqTermM TyInst{}   _ = empty
eqTermM Var{}      _ = empty
eqTermM Constant{} _ = empty
eqTermM Builtin{}  _ = empty

-- | Check equality of two 'Program's.
eqProgramM
    :: (GEq uni, Closed uni, uni `Everywhere` Eq)
    => EqRenameOf ScopedEtaMapping (Program tyname name uni ann)
eqProgramM (Program _ ver1 term1) (Program _ ver2 term2) = do
    guard $ ver1 == ver2
    eqTermM term1 term2
