{-# LANGUAGE GADTs            #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module Universe.Poly
    ( TypeApp
    , HasUniApply (..)
    , asTypeApp
    , withDecodedTypeApp
    , asTypeFun
    , withDecodedTypeFun
    ) where

import           Universe.Core

import           Data.Kind
import           Data.Type.Equality
import           Type.Reflection

{- Note [Representing polymorphism]
Consider the following universe:

    data U a where
        UList :: !(U a) -> U [a]
        UInt  :: U Int

It has ints and polymorphic lists in it (including lists of lists etc).

This representation works perfectly at the value level, you can instantiate functions like

    foo :: (uni `Includes` [], uni `Includes` Int) => <...>
    foo = <...>

with 'U', it is straightforward to provide a meaninful 'Closed' instance etc. I.e. at the value
level polymorphic data types are entirely unproblematic, since they are always fully instantiated
there and so there's basically no difference compared to regular monomorphic types.

However if you also have the type level in your target language (i.e. it's not some form of an
untyped calculus) and the type language supports polymorphism and you have polymorphic built-in
functions, then the version of 'U' from the above does not fit as well. For example, you want
to be able to represent the following built-in function:

    idList :: forall a. [a] -> [a]  -- In the source language (Haskell)
    idList : all a. [a] -> [a]      -- In the target language

It's obvious how to implement the former, but for the latter you have to put a target language
variable (@a@) into a meta type (@[]@), which is not only awkward, but also requires a lot of extra
care in every part of the compiler that deals with types, for example in this setting type
substitution has to look inside built-in types (and for that reason you have to be able to store
not just type variables but full target language types in meta types, 'cause otherwise you can't
substitute a type for a type variable and so substitution is broken). So this is really tricky.

However instead of putting target language type variables into meta types we can instead have
type lambdas inside universes, or, even better, Agda-like operators sections
(see https://agda.readthedocs.io/en/v2.6.1.3/language/mixfix-operators.html#mixfix-operators).
For that we only need to add another constructor to 'U':

    data Hole  -- An empty data type.

    data U a where
        <...>
        UHole :: U Hole

That allows us to put @UList UHole@ into a target language type, which displays as @[_]@ and means
@\a -> [a]@, which is a neutral (as in, irreducible) type-level function that we can apply via the
regular type-level function application constructor, which allows us not to put the argument into
the meta type, but instead keep it in the type AST. If we wanted to add pairs as built-in types,
we'd add the following constructor:

    data U a where
        <...>
        UPair :: !(U a) -> !(U b) -> U (a, b)

and here are some examples of meta types and what they'd mean in the target language:

    UPair UInt  (UList UInt)        (Int, [Int])
    UPair UInt  UHole               \b -> (Int, b)
    UPair UHole (UList UInt)        \a -> (a, [Int])
    UPair UHole UHole               \a b -> (a, b)

Overall, we need to be careful not to end up using 'UHole' at the term level, and some rather
boilerplate-y infrastructure is required to connect the type and term levels of the target
language (as you need to manually check if an argument to a built-in function is a list/pair as
expected, because with this solution there's no general way (or at least I haven't found one)
to match types of arguments against arbitrary-kinded applied type operator sections), but otherwise
this solution does make it possible to apply meta types to target language types without infecting
the former with the latter.

Things however become more complex if you want to be polymorphic over universes in your target
language. You can no longer match against a handful of hardcoded type tags. You could introduce type
classes like @UniHasList@, @UniHasPair@ etc, but having a class per polymorphic built-in type is
clunky and boilerplate-y (and this is in addition to the existing boilerplate-y infrastructure
that was mentioned above). It would be nice if we could impose each universe to have a single
application constructor and not require polymorphic built-in types to be fully applied at all
times ("fully applied" includes "applied to a hole").

2. forall k. k -> *
3. data T = forall k. T k
4. TypeApp
5. as data family
6. as type family
7. non-erasable types
-}

-- | A (possibly partial) type application.
data TypeApp (a :: k)

class HasUniApply (uni :: Type -> Type) where
    matchUniRunTypeApp
        :: uni a
        -> r
        -> (uni (TypeApp a) -> r)
        -> r
    matchUniApply
        :: uni tfa
        -> r
        -> (forall k f a. tfa ~ TypeApp (f a :: k) => uni (TypeApp f) -> uni a -> r)
        -> r

asTypeApp
    :: forall uni ta m r. (Typeable ta, MonadFail m)
    => uni ta
    -> (forall (a :: Type). (ta ~ TypeApp a, Typeable a) => m r)
    -> m r
asTypeApp _ k = do
    App repT repA <- pure $ typeRep @ta
    let kindA = typeRepKind repA
        repT' = withTypeable kindA $ typeRep @TypeApp
    Just Refl <- pure $ repT `testEquality` repT'
    Just Refl <- pure $ typeRepKind repA `testEquality` typeRep @Type
    withTypeable repA k

withDecodedTypeApp
    :: forall uni r. Closed uni
    => (forall (a :: Type). Typeable a => uni (TypeApp a) -> DecodeUniM r)
    -> DecodeUniM r
withDecodedTypeApp k = withDecodedUni @uni $ \uniTA -> asTypeApp uniTA $ k uniTA

-- We only need this function, because GHC won't allow turning @repF@ into the @Typeable f@
-- constraint at the end of the definition for whatever stupid reason. So we do that in 'asTypeFun'.
withTypeFunRep
    :: forall proxy tf m r. (Typeable tf, MonadFail m)
    => proxy tf
    -> (forall k (f :: Type -> k). (tf ~ TypeApp f, Typeable k) => TypeRep f -> m r)
    -> m r
withTypeFunRep _ k = do
    App repT repF <- pure $ typeRep @tf
    let kindF = typeRepKind repF
    Fun repArg repRes <- pure kindF
    let repT' = withTypeable kindF $ typeRep @TypeApp
    Just Refl  <- pure $ repT `testEquality` repT'
    Just HRefl <- pure $ repArg `eqTypeRep` typeRep @Type
    Just Refl  <- pure $ typeRepKind repRes `testEquality` typeRep @Type
    withTypeable repRes $ k repF

asTypeFun
    :: forall proxy tf m r. (Typeable tf, MonadFail m)
    => proxy tf
    -> (forall k (f :: Type -> k). (tf ~ TypeApp f, Typeable k, Typeable f) => m r)
    -> m r
asTypeFun uniF k = withTypeFunRep uniF $ \repF -> withTypeable repF k

withDecodedTypeFun
    :: forall uni r. Closed uni
    => (forall k (f :: Type -> k). (Typeable k, Typeable f) => uni (TypeApp f) -> DecodeUniM r)
    -> DecodeUniM r
withDecodedTypeFun k = withDecodedUni @uni $ \uniF -> asTypeFun uniF $ k uniF
