{-# LANGUAGE GADTs            #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module Universe.Poly
    ( HasUniApply (..)
    , checkStar
    , withApplicable
    , (:~:)(..)
    ) where

import           Universe.Core

import           Data.Kind
import           Data.Type.Equality
import           Type.Reflection

{- Note [Representing polymorphism]
Consider the following universe (in this example and the ones belwo bangs on arguments in universes
are omitted for clarity):

    data U a where
        UList :: U a -> U [a]
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
        UPair :: U a -> U b -> U (a, b)

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

So can we index the universe by types of arbitrary kinds and have a single application constructor?
Well, we can define

    data U (a :: k) where
        UProtoList :: U []
        UInt       :: U Int
        UApply     :: U f -> U a -> U (f a)

which allows us to recover the original 'UList' as

    pattern UList = UApply UProtoList

But 'U' is of kind @forall k. k -> Type@, which is really hard to deal with. For one thing, we lose
pretty much any interop with the rest of the ecosystem, for example not only is it not possible to
derive 'GEq' or 'GShow' anymore, it's not even correct to say @GEq U@, because 'GEq' expects
something of type @k -> Type@ for a particular @k@, while 'U' has a different kind.

Our problems with 'U' don't end here. Having a @forall@ in the kind destroys type inference.
For example, having

    type ISome :: (forall k. k -> Type) -> Type
    data ISome f = forall a (x :: a). ISome (f x)

    data U (a :: k)

we can check that

    newtype TypeIn uni a = TypeIn (uni a)

    type Test = ISome (TypeIn U)

type checks just fine when 'TypeIn' has the following kind signature:

    type TypeIn :: (forall k. k -> Type) -> forall l. l -> Type

but fails to type check when the final @forall@ is moved to the left:

    type TypeIn :: forall l. (forall k. k -> Type) -> l -> Type

We could fix it by defining

    type IType = forall k. k -> Type

and using it everywhere instead of @forall k. k -> Type@, but our problems just start here.
For another example, the following does not type check at all:

    type IType = forall k. k -> Type

    type IValueOf :: IType -> Type -> Type
    data IValueOf uni a = IValueOf (uni a) a

    instance Eq (IValueOf (uni :: IType) a)

GHC does not seem to like that implicitly quantified @uni@ has a higher-rank kind.
And it's annoying that we'd need both @Some@ (for values) and @ISome@ (for types).

So basically this approach is unusable.

But there's another way to spell @forall k. k -> Type@ and it's @(exists k. k) -> Type@ or in
Haskell terms:

    data T = forall k. T k

    data U (a :: T) where
        UProtoList :: U ('T [])
        UInt       :: U ('T Int)
        UApply     :: U ('T f) -> U ('T a) -> U ('T (f a))

This however this variant of 'U' has the disadvantage of not being of the @Type -> Type@ kind
(it's @T -> Type@ instead), which means we now need to introduce kind polymorphism in 'Some',
'TypeIn', 'Includes' and every other part of the infrastructure, which complicates the encoding.
But it's trivial to fix that: we can think of @Type@ as a data type itself whose constructors
(an infinite amount of them) are things introduced via the @data@ keyword. This gives us

    data T (a :: k)

    data U (a :: Type) where
        UProtoList :: U (T [])
        UInt       :: U (T Int)
        UApply     :: U (T f) -> U (T a) -> U (T (f a))

This one seems to be good enough, however adopting this strategy requires reworking the whole
infrastructure. For example, 'ValueOf' has to change from

    data ValueOf uni a = ValueOf (uni a) a

to

    data ValueOf uni a = ValueOf (uni (T a)) a

and we need to introduce @IType@ mentioned above, provide two versions of 'Some' etc. And it's
annoying that if we want to talk about partially applied type constructors, then suddenly we need
a completely different encoding of universes (and of the whole infrastructure) than the one that we
used before we had type constructors (or cared about partially applying them). Maybe the annoyance
is worth it, but I've opted for a slightly different encoding that allows us to keep the old
infrastructure and only add a bit of stuff on top of it at the expense of slightly complicating
user code (generally, not a good trade-off, I know). Ok, so the idea is that we only "shield" those
types that are of a higher-kind instead of applying @T@ to every single type in the universe. I.e.
we specifically embed into @Type@ only (possibly partial) type applications and add one more
constructor that allows for "running" such applications:

    data T

    data U (a :: Type) where
        UProtoList  :: U (T [])
        UInt        :: U Int
        UApply      :: U (T f) -> U a -> U (T (f a))
        URunT :: U (T a) -> U a





2. forall k. k -> *
3. data T = forall k. T k
4. T
5. as data family
6. as type family
7. non-erasable types

GEq, GShow

data Uni (a :: k)

type Test = SomeH (TypeInH Uni)

-- | Existential quantification as a data type.
type SomeH :: (forall k. k -> Type) -> Type
data SomeH f = forall k (a :: k). SomeH (f a)

-- | Existential quantification as a data type.
-- type TypeInH :: (forall k. k -> Type) -> forall k. k -> Type
-- newtype TypeInH uni x = TypeInH (uni x)


type IType = forall k. k -> Type

-- | Existential quantification as a data type.
type ISome :: IType -> Type
data ISome f = forall a (x :: a). ISome (f x)

-- | Existential quantification as a data type.
type Some :: (Type -> Type) -> Type
data Some f = forall x. Some (f x)

-- | A particular type from a universe.
type TypeIn :: IType -> IType
newtype TypeIn uni a = TypeIn (uni a)

-- | A value of a particular type from a universe.
type ValueOf :: IType -> Type -> Type
data ValueOf uni a = ValueOf (uni a) a


-- Explicit IType
someValueOf :: forall a (uni :: IType). uni a -> a -> Some (ValueOf uni)


instance GEq (ValueOf (uni :: IType)) where


-}

class HasUniApply (uni :: Type -> Type) where
    matchUniApply
        :: uni tb
        -> r
        -> (forall k l (f :: k -> l) a. tb ~ T (f a) => uni (T f) -> uni (T a) -> r)
        -> r

checkStar :: forall uni a (x :: a). Typeable a => uni (T x) -> Maybe (a :~: Type)
checkStar _ = typeRep @a `testEquality` typeRep @Type

withApplicable
    :: forall (a :: Type) (ab :: Type) f x uni m r. (Typeable ab, Typeable a, MonadFail m)
    => uni (T (f :: ab))
    -> uni (T (x :: a))
    -> (forall (b :: Type). (Typeable b, ab ~ (a -> b)) => m r)
    -> m r
withApplicable _ _ k = do
    Fun repA repB <- pure $ typeRep @ab
    -- Why do we need these two?
    Just HRefl <- pure $ typeRepKind repA `eqTypeRep` typeRep @Type
    Just HRefl <- pure $ typeRepKind repB `eqTypeRep` typeRep @Type
    Just Refl <- pure $ typeRep @a `testEquality` repA
    withTypeable repB k


-- asTypeFun
--     :: forall proxy tf m r. (Typeable tf, MonadFail m)
--     => proxy tf
--     -> (forall k (f :: Type -> k). (tf ~ T f, Typeable k, Typeable f) => m r)
--     -> m r
-- asTypeFun uniF k = undefined -- withTypeFunRep uniF $ \repF -> withTypeable repF k

-- withDecodedTypeFun
--     :: forall uni r. Closed uni
--     => (forall k l (f :: k -> l). (Typeable k, Typeable l) => uni (T f) -> DecodeUniM r)
--     -> DecodeUniM r
-- withDecodedTypeFun k = undefined -- withDecodedUni @uni $ \uniF -> asTypeFun uniF $ k uniF

-- kindOfArgument :: forall k l (f :: k -> l) uni. Typeable k => uni (T f) -> TypeRep k
-- kindOfArgument _ = typeRep

-- kindOf :: forall k (a :: k) uni. Typeable k => uni (T a) -> TypeRep k
-- kindOf _ = typeRep

-- applicable
--     :: forall a b c f x uni m. (Typeable a, Typeable b, Alternative m)
--     => uni (T (f :: b -> c)) -> uni (T (x :: a)) -> m (a :~: b)
-- applicable _ _ = maybe empty pure $ typeRep @a `testEquality` typeRep @b


-- testEqualityProxy :: (Typeable a, Typeable b) => Proxy a -> Proxy b -> Maybe (a :~: b)
-- testEqualityProxy = undefined

-- TestEquality

-- asT
--     :: forall uni ta m r. (Typeable ta, MonadFail m)
--     => uni ta
--     -> (forall (a :: Type). (ta ~ T a, Typeable a) => m r)
--     -> m r
-- asT _ k = do
--     App repT repA <- pure $ typeRep @ta
--     let kindA = typeRepKind repA
--         repT' = withTypeable kindA $ typeRep @T
--     Just Refl <- pure $ repT `testEquality` repT'
--     Just Refl <- pure $ typeRepKind repA `testEquality` typeRep @Type
--     withTypeable repA k

-- withDecodedT
--     :: forall uni r. Closed uni
--     => (forall (a :: Type). Typeable a => uni (T a) -> DecodeUniM r)
--     -> DecodeUniM r
-- withDecodedT k = withDecodedUni @uni $ \uniTA -> asT uniTA $ k uniTA

-- -- We only need this function, because GHC won't allow turning @repF@ into the @Typeable f@
-- -- constraint at the end of the definition for whatever stupid reason. So we do that in 'asTypeFun'.
-- withTypeFunRep
--     :: forall proxy tf m r. (Typeable tf, MonadFail m)
--     => proxy tf
--     -> (forall k (f :: Type -> k). (tf ~ T f, Typeable k) => TypeRep f -> m r)
--     -> m r
-- withTypeFunRep _ k = do
--     App repT repF <- pure $ typeRep @tf
--     let kindF = typeRepKind repF
--     Fun repArg repRes <- pure kindF
--     let repT' = withTypeable kindF $ typeRep @T
--     Just Refl  <- pure $ repT `testEquality` repT'
--     Just HRefl <- pure $ repArg `eqTypeRep` typeRep @Type
--     Just Refl  <- pure $ typeRepKind repRes `testEquality` typeRep @Type
--     withTypeable repRes $ k repF

-- asTypeFun
--     :: forall proxy tf m r. (Typeable tf, MonadFail m)
--     => proxy tf
--     -> (forall k (f :: Type -> k). (tf ~ T f, Typeable k, Typeable f) => m r)
--     -> m r
-- asTypeFun uniF k = withTypeFunRep uniF $ \repF -> withTypeable repF k

-- withDecodedTypeFun
--     :: forall uni r. Closed uni
--     => (forall k (f :: Type -> k). (Typeable k, Typeable f) => uni (T f) -> DecodeUniM r)
--     -> DecodeUniM r
-- withDecodedTypeFun k = withDecodedUni @uni $ \uniF -> asTypeFun uniF $ k uniF
