{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}
-- Required only by 'Permits0' for some reason.
{-# LANGUAGE UndecidableSuperClasses  #-}

module Universe.Core
    ( Esc
    , Some (..)
    , SomeTypeIn (..)
    , Kinded (..)
    , ValueOf (..)
    , someValueOf
    , someValue
    , Contains (..)
    , Includes
    , DecodeUniM (..)
    , Closed (..)
    , decodeKindedUni
    , peelUniTag
    , Permits
    , EverywhereAll
    , type (<:)
    , HasUniApply (..)
    , checkStar
    , withApplicable
    , knownUniOf
    , GShow (..)
    , gshow
    , GEq (..)
    , deriveGEq
    , (:~:)(..)
    ) where

import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Trans.State.Strict
import           Data.GADT.Compare
import           Data.GADT.Compare.TH
import           Data.GADT.Show
import           Data.Hashable
import           Data.Kind
import           Data.Proxy
import           Data.Type.Equality
import           Text.Show.Deriving
import           Type.Reflection

{- Note [Universes]
A universe is a collection of tags for types. It can be finite like

    data U a where
        UUnit :: U ()
        UInt  :: U Int

(where 'UUnit' is a tag for '()' and 'UInt' is a tag for 'Int') or infinite like

    data U a where
        UBool :: U Bool
        UList :: !(U a) -> U [a]

Here are some values of the latter 'U' / the types that they encode

        UBool               / Bool
        UList UBool         / [Bool]
        UList (UList UBool) / [[Bool]]

'U' being a GADT allows us to package a type from a universe together with a value of that type.
For example,

    Some (ValueOf UBool True) :: Some (ValueOf U)

We say that a type is in a universe whenever there is a tag for that type in the universe.
For example, 'Int' is in 'U', because there exists a tag for 'Int' in 'U' ('UInt').
-}

{- Note [Representing polymorphism]
Consider the following universe (in this example and the ones below bangs on arguments in universes
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

    data Esc = forall k. Esc k

    data U (a :: T) where
        UProtoList :: U ('Esc [])
        UInt       :: U ('Esc Int)
        UApply     :: U ('Esc f) -> U ('Esc a) -> U ('Esc (f a))

However this variant of 'U' has the disadvantage of not being of the @Type -> Type@ kind
(it's @T -> Type@ instead), which means that the user now needs to enable @DataKinds@ just to be
able to mention universes (even without actually doing anything with them) and also use those
annoying ticks. So instead we can think of @Type@ as a data type itself whose constructors
(an infinite amount of them) are things introduced via the @data@ keyword. This gives us

    data Esc (a :: k)

    data U (a :: Type) where
        UProtoList :: U (Esc [])
        UInt       :: U (Esc Int)
        UApply     :: U (Esc f) -> U (Esc a) -> U (Esc (f a))

(note that we haven't introduced any more "openness" with this trick as any kind in Haskell is
already weirdly open (including @T@): https://gist.github.com/ekmett/ac881f3dba3f89ec03f8fdb1d8bf0a40)

This is the encoding that we use, but unfortunately that required reworking the whole infrastructure
that we originally had. For example, 'ValueOf' had to change from

    data ValueOf uni a = ValueOf (uni a) a

to

    data ValueOf uni a = ValueOf (uni (Esc a)) a

It is annoying that if we want to talk about partially applied type constructors, then suddenly we
need a completely different encoding of universes (and of the whole infrastructure) than the one
that we used before we had type constructors (or cared about partially applying them), but I believe
it's worth the trouble.
-}

{- Note [Decoding universes]
We have types of arbitrary kinds at the type level, but at the value level every constant must be of
kind star. I.e. we have to be able to parse/decode arbitrary types, but ensure that a decoded type
is of kind star whenever we expect to parse/decode a constant of that type next. This is one reason
why we have all these 'Typeable' constraints lying around.

Type-wise this is enforced via 'bring' expecting a @uni (Esc a)@ with @a@ being of kind @Type@.
I.e. there is no way one could parse a general type and then attempt to bring a constraint for
that type in scope via 'bring' without first ensuring that the type is of kind star.

Another reason for having the 'Typeable' constraints is that decoding a type application requires
checking that the expected kind of an argument matches the kind of the provided argument due to us
having an intrinsically-kinded reprensentation of types.
-}

{- Note [The TypeApp approach]
There's an alternative approach to representing universes supporting partial application of
type constructors. The idea is that we only "shield" those types that are of a non-star kind instead
of applying @T@ to every single type in the universe. I.e. we specifically embed into @Type@ only
(possibly partial) type applications and add one more constructor that allows for "running" such
applications:

    data TypeApp (a :: k)

    data U (a :: Type) where
        UProtoList  :: U (TypeApp [])
        UInt        :: U Int
        UApply      :: U (TypeApp f) -> U a -> U (TypeApp (f a))
        URunTypeApp :: U (TypeApp a) -> U a

This representation has the advantage of allowing for sharing the universes infrastructure between
the monomorphic and polymorphic cases. I.e. we could use good old

    data ValueOf uni a = ValueOf (uni a) a

instead of having to use the slightly more awkward

    data ValueOf uni a = ValueOf (uni (Esc a)) a

One problem that this representation has is redundancy: there are two ways to represent the type
of lists of integers (for some definition of @SomeTypeIn@):

    SomeTypeIn (URunTypeApp (UProtoList `UApply` UInt))
    SomeTypeIn (UProtoList `UApply` UInt)

In practice it's not a big deal, we just need not to forget to strip the 'URunTypeApp' constructor
off whenever that is important (for example, during type normalization).

But a more serious problem with this representation is that we lose all the type safety discussed
in Note [Decoding universes], which makes it rather easy to shoot oneself in the foot with
@error "not supposed to happen"@ happening. I.e. we'd need to perform all the same checks
in client code but without the type checker forcing us to do so like it does now, so that's a huge
price to pay for some superficial syntactic nicety and hence we choose the safe approach,
even though that required reworking all the infrastructure in a backwards-incompatible manner.
-}

-- See Note [Representing polymorphism].
-- | \"Escapes\" a type of an arbitrary kind to fit into 'Type'.
type Esc :: forall k. k -> Type
data Esc a

-- | Existential quantification as a data type.
type Some :: forall a. (a -> Type) -> Type
data Some f = forall x. Some !(f x)

-- | A particular type from a universe.
type SomeTypeIn :: (Type -> Type) -> Type
data SomeTypeIn uni = forall k (a :: k). SomeTypeIn !(uni (Esc a))

data Kinded uni ta where
    Kinded :: Typeable k => !(uni (Esc a)) -> Kinded uni (Esc (a :: k))

-- | A value of a particular type from a universe.
type ValueOf :: (Type -> Type) -> Type -> Type
data ValueOf uni a = ValueOf !(uni (Esc a)) !a

{- | A class for enumerating types and fully instantiated type formers that @uni@ contains.
For example, a particular @ExampleUni@ may have monomorphic types in it:

    instance ExampleUni `Contains` Integer where <...>
    instance ExampleUni `Contains` Bool    where <...>

as well as polymorphic ones:

    instance ExampleUni `Contains` [] where <...>
    instance ExampleUni `Contains` (,) where <...>

as well as their instantiations:

    instance ExampleUni `Contains` a => ExampleUni `Contains` [a] where <...>
    instance (ExampleUni `Contains` a, ExampleUni `Contains` b) => ExampleUni `Contains` (a, b) where <...>

(a universe can have any subset of the mentioned sorts of types, for example it's fine to have
instantiated polymorphic types and not have uninstantiated ones and vice versa)

Note that when used as a constraint of a function 'Contains' does not allow you to directly
express things like \"@uni@ has the @Integer@, @Bool@ and @[]@ types and type formers\",
because @[]@ is not fully instantiated. So you can only say \"@uni@ has @Integer@, @Bool@,
@[Integer]@, @[Bool]@, @[[Integer]]@, @[[Bool]]@ etc\" and such manual enumeration is annoying,
so we'd really like to be able to say that @uni@ has lists of arbitrary built-in types
(including lists of lists etc). 'Contains' does not allow that, but 'Includes' does.
For example, in the body of the following definition:

    foo :: (uni `Includes` Integer, uni `Includes` Bool, uni `Includes` []) => <...>
    foo = <...>

you can make use of the fact that @uni@ has lists of arbitrary included types (integers,
booleans and lists).

Hence most of the time opt for using the more flexible 'Includes'.

'Includes' is defined in terms of 'Contains', so you only need to provide a 'Contains' instance
per type from the universe and you'll get 'Includes' for free.
-}
type Contains :: forall k. (Type -> Type) -> k -> Constraint
class uni `Contains` a where
    knownUni :: uni (Esc a)

{- Note [The definition of Includes]
We need to be able to partially apply 'Includes' (required in the definition of '<:' for example),
however if we define 'Includes' as a class alias like that:

    class    Contains uni `Permits` a => uni `Includes` a
    instance Contains uni `Permits` a => uni `Includes` a

we get this extra annoying warning:

    • The constraint ‘Includes uni ()’ matches
        instance forall k (uni :: * -> *) (a :: k).
                 Permits (Contains uni) a =>
                 Includes uni a
      This makes type inference for inner bindings fragile;
        either use MonoLocalBinds, or simplify it using the instance

at the use site, so instead we define 'Includes' as a type alias of one argument (i.e. 'Includes'
has to be immediately applied only to a @uni@ at the use site).
-}

-- See Note [The definition of Includes].
-- | @uni `Includes` a@ reads as \"@a@ is in the @uni@\". @a@ can be of a higher-kind,
-- see the docs of 'Contains' on why you might want that.
type Includes :: forall k. (Type -> Type) -> k -> Constraint
type Includes uni = Permits (Contains uni)

-- | Same as 'knownUni', but receives a @proxy@.
knownUniOf :: uni `Contains` a => proxy a -> uni (Esc a)
knownUniOf _ = knownUni

-- | Wrap a value into @Some (ValueOf uni)@, given its explicit type tag.
someValueOf :: forall a uni. uni (Esc a) -> a -> Some (ValueOf uni)
someValueOf uni = Some . ValueOf uni

-- | Wrap a value into @Some (ValueOf uni)@, provided its type is in the universe.
someValue :: forall a uni. uni `Includes` a => a -> Some (ValueOf uni)
someValue = someValueOf knownUni

-- | A monad to decode types from a universe in.
-- We use a monad for decoding, because parsing arguments of polymorphic built-in types can peel off
-- an arbitrary amount of type tags from the input list of tags and so we have state, which is
-- convenient to handle with, well, 'StateT'.
newtype DecodeUniM a = DecodeUniM
    { unDecodeUniM :: StateT [Int] Maybe a
    } deriving newtype (Functor, Applicative, Alternative, Monad, MonadPlus, MonadFail)

runDecodeUniM :: [Int] -> DecodeUniM a -> Maybe (a, [Int])
runDecodeUniM is (DecodeUniM a) = runStateT a is

-- | A universe is 'Closed', if it's known how to constrain every type from the universe and
-- every type can be encoded to / decoded from a sequence of integer tags.
-- The universe doesn't have to be finite and providing support for infinite universes is the
-- reason why we encode a type as a sequence of integer tags as opposed to a single integer tag.
-- For example, given
--
-- >   data U a where
-- >       UList :: !(U a) -> U [a]
-- >       UInt  :: U Int
--
-- @UList (UList UInt)@ can be encoded to @[0,0,1]@ where @0@ and @1@ are the integer tags of the
-- @UList@ and @UInt@ constructors, respectively.
class Closed uni where
    -- | A constrant for \"@constr a@ holds for any @a@ from @uni@\".
    type Everywhere uni (constr :: Type -> Constraint) :: Constraint

    -- | Encode a type as a sequence of 'Int' tags.
    -- The opposite of 'decodeUni'.
    encodeUni :: uni a -> [Int]

    -- | Decode a type and feed it to the continuation.
    withDecodedUni :: (forall k (a :: k). Typeable k => uni (Esc a) -> DecodeUniM r) -> DecodeUniM r

    -- | Bring a @constr a@ instance in scope, provided @a@ is a type from the universe and
    -- @constr@ holds for any type from the universe.
    bring :: uni `Everywhere` constr => proxy constr -> uni (Esc a) -> (constr a => r) -> r

-- | Decode a type from a sequence of 'Int' tags.
-- The opposite of 'encodeUni' (modulo invalid input).
decodeKindedUni :: Closed uni => [Int] -> Maybe (SomeTypeIn (Kinded uni))
decodeKindedUni is = do
    (x, []) <- runDecodeUniM is $ withDecodedUni $ pure . SomeTypeIn . Kinded
    pure x

-- >>> runDecodeUniM [1,2,3] peelUniTag
-- Just (1,[2,3])
-- >>> runDecodeUniM [] peelUniTag
-- Nothing
-- | Peel off a tag from the input list of type tags.
peelUniTag :: DecodeUniM Int
peelUniTag = DecodeUniM $ do
    i:is <- get
    i <$ put is

-- It's not possible to return a @forall@ from a type family, let alone compute a proper
-- quantified context, hence the boilerplate and a finite number of supported cases.

type Permits0 :: (Type -> Constraint) -> Type -> Constraint
class    constr x => constr `Permits0` x
instance constr x => constr `Permits0` x

type Permits1 :: (Type -> Constraint) -> (Type -> Type) -> Constraint
class    (forall a. constr a => constr (f a)) => constr `Permits1` f
instance (forall a. constr a => constr (f a)) => constr `Permits1` f

type Permits2 :: (Type -> Constraint) -> (Type -> Type -> Type) -> Constraint
class    (forall a b. (constr a, constr b) => constr (f a b)) => constr `Permits2` f
instance (forall a b. (constr a, constr b) => constr (f a b)) => constr `Permits2` f

type Permits3 :: (Type -> Constraint) -> (Type -> Type -> Type -> Type) -> Constraint
class    (forall a b c. (constr a, constr b, constr c) => constr (f a b c)) => constr `Permits3` f
instance (forall a b c. (constr a, constr b, constr c) => constr (f a b c)) => constr `Permits3` f

-- I tried defining 'Permits' as a class but that didn't have the right inference properties
-- (i.e. I was getting errors in existing code). That probably requires bidirectional instances
-- to work, but who cares given that the type family version works alright and can even be
-- partially applied (the kind has to be provided immediately though, but that's fine).
{- | @constr `Permits` f@ elaborates to one of
-
    constr f
    forall a. constr a => constr (f a)
    forall a b. (constr a, constr b) => constr (f a b)
    forall a b c. (constr a, constr b, constr c) => constr (f a b c)

depending on the kind of @f@. This allows us to say things like

   ( constr `Permits` Integer
   , constr `Permits` []
   , constr `Permits` (,)
   )

and thus constraint every type from the universe (including polymorphic ones) to satisfy
@constr@, which is how we provide an implementation of 'Everywhere' for universes with
polymorphic types.

'Permits' is an open type family, so you can provide type instances for @f@s expecting
more type arguments than 3 if you need that.

Note that, say, @constr `Permits` []@ elaborates to

    forall a. constr a => constr [a]

and for certain type classes that does not make sense (e.g. the 'Generic' instance of @[]@
does not require the type of elements to be 'Generic'), however it's not a problem because
we use 'Permit' to constrain the whole universe and so we know that arguments of polymorphic
built-in types are builtins themselves are hence do satisfy the constraint and the fact that
these constraints on arguments do not get used in the polymorphic case only means that they
get ignored.
-}
type Permits :: forall k. (Type -> Constraint) -> k -> Constraint
type family Permits

-- Implicit pattern matching on the kind.
type instance Permits = Permits0
type instance Permits = Permits1
type instance Permits = Permits2
type instance Permits = Permits3

-- We can't use @All (Everywhere uni) constrs@, because 'Everywhere' is an associated type family
-- and can't be partially applied, so we have to inline the definition here.
type EverywhereAll :: (Type -> Type) -> [Type -> Constraint] -> Constraint
type family uni `EverywhereAll` constrs where
    uni `EverywhereAll` '[]                 = ()
    uni `EverywhereAll` (constr ': constrs) = (uni `Everywhere` constr, uni `EverywhereAll` constrs)

-- | A constraint for \"@uni1@ is a subuniverse of @uni2@\".
type uni1 <: uni2 = uni1 `Everywhere` Includes uni2

-- | A class for \"@uni@ has general type application\".
class HasUniApply (uni :: Type -> Type) where
    -- | Deconstruct a type application into the function and the argument and feed them to the
    -- continuation. If the type is not an application, then return the default value.
    matchUniApply
        :: uni tb  -- ^ The type.
        -> r       -- ^ What to return if the type is not an application.
        -> (forall k l (f :: k -> l) a. tb ~ Esc (f a) => uni (Esc f) -> uni (Esc a) -> r)
                   -- ^ The continuation taking a function and an argument.
        -> r

-- See Note [Decoding universes].
-- You might think @uni@ is inferrable from the explicitly given argument. Nope, in most cases it's
-- not. It seems, kind equalities mess up inference.
-- | Check if the kind of the given type from the universe is 'Type'.
checkStar :: forall uni a (x :: a). Typeable a => uni (Esc x) -> Maybe (a :~: Type)
checkStar _ = typeRep @a `testEquality` typeRep @Type

fromJustM :: MonadPlus f => Maybe a -> f a
fromJustM = maybe mzero pure

-- See Note [Decoding universes].
-- | Check if one type from the universe can be applied to another (i.e. check that the expected
-- kind of the argument matches the actual one) and call the continuation in the refined context.
-- Fail with 'mzero' otherwise.
withApplicable
    :: forall (a :: Type) (ab :: Type) f x uni m r. (Typeable ab, Typeable a, MonadPlus m)
    => uni (Esc (f :: ab))
    -> uni (Esc (x :: a))
    -> (forall (b :: Type). (Typeable b, ab ~ (a -> b)) => m r)
    -> m r
withApplicable _ _ k =
    case typeRep @ab of
        Fun repA repB -> do
            -- The type of @(->)@ is
            --
            --     forall {r1} {r2} (a :: TYPE r1) (b :: TYPE r2). a -> b -> Type
            --
            -- so we need to demonstrate that both @a@ and @b@ are of kind @Type@. We get the former
            -- from checking that the type representation of 'withApplicable'-bound @a@ equals @a@
            -- from @a -> b@, but for the latter we need an explicit check.
            HRefl <- fromJustM $ typeRep @a `eqTypeRep` repA
            Refl <- fromJustM $ typeRepKind repB `testEquality` typeRep @Type
            withTypeable repB k
        _ -> mzero

{- Note [The G, the Tag and the Auto]
Providing instances for

    data Some f = forall a. Some (f a)

is tricky. There are several things to consider here:

1. the G: for some type classes we can provide an instance for @Some f@ for any @f@ generically.
Take for example @Show (Some f)@, we could implement it as

    instance (forall a. Show (f a)) => Show (Some f) where
        show (Some a) = "Some " ++ show a

(with `-XQuantifiedConstraints`). Unfortunately, that breaks @deriving (Show)@ for every data type
that has @Some f@ somewhere inside it and forces you to use a standalone deriving declaration for
each such data type, which is rather annoying, because instance contexts tend to get huge,
so it takes time to come up with them or to remember where to copy them from and they also occupy
a lot of space (text-wise).

Luckily, "Data.GADT.Show" provides

    class GShow t where
        gshowsPrec :: Int -> t a -> ShowS

    gshow :: GShow t => t a -> String

which allows us to define a 'Show' instance for 'Some' as

    instance GShow f => Show (Some f) where
        show (Some a) = "Some " ++ gshow a

so @GShow f@ is basically an encoding of @forall a. Show (f a)@.

2. the Tag: for some type classes we can get away without providing the G version of a type class,
e.g. 'Hashable' is handled like that:

    instance Closed uni => Hashable (TypeIn uni a) where
        hashWithSalt salt (TypeIn uni) = hashWithSalt salt $ encodeUni uni

    instance Closed uni => Hashable (SomeTypeIn uni) where
        hashWithSalt salt (Some s) = hashWithSalt salt s

where

    class Closed uni where
        encodeUni :: uni a -> [Int]
        <...>

So as long as for each type of a universe you know its encoding as a sequence of integer tags,
you can hash any type from the universe via that sequence. 'Serialise' is handled in a similar way.

The 'Hashable' type class is also interesting in that we do not provide a generic instance for
any @Some f@. This is because @f@ can be anything of kind @* -> *@ and we only have 'encodeUni' for
universes. In order to stress that the @f@ in this instance has to be a universe we use
the 'TypeIn' wrapper:

    instance Closed uni => Hashable (SomeTypeIn uni) where

This allows us to hash a type from a universe and a value of a type from a universe in different
ways. The latter instance looks like this:

    instance (Closed uni, uni `Everywhere` Hashable) => Hashable (ValueOf uni a) where
        hashWithSalt salt (ValueOf uni x) =
            bring (Proxy @Hashable) uni $ hashWithSalt salt (SomeTypeIn uni, x)

    instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Some (ValueOf uni)) where
        hashWithSalt salt (Some s) = hashWithSalt salt s

Here we hash a 'ValueOf' value as a pair of a type from a universe and a value of that type.

Another type class for which a generic @Some f@ instance doesn't make sense is 'NFData'.
For universes we define

    instance NFData (TypeIn uni a) where
        rnf (TypeIn uni) = rnf $ encodeUni uni

    instance NFData (SomeTypeIn uni) where
        rnf (Some s) = rnf s

i.e. to fully force a type from a universe it's enough to encode the type as a sequence of integer
tags and fully force that sequence.

3. the Auto:

When we can manually provide an instance for a type class, the two previous approaches work nicely.
But for a type class like 'Lift' we really want to use the deriving mechanism in order not to mess
with the hairy internal representation ('Exp' and stuff). But 'deriveLift' (and 'makeLift') calls
'lift' under the hood while we want it to call 'glift'. So we define a newtype wrapper ('AG') that
implements 'Lift' in terms of 'GLift', insert the 'AG' constructor in the right place and invoke
'makeLift' which calls 'lift' on 'AG' internally, so the 'lift' gets elaborated to 'glift'
as we want it to.

And even though we can manually write 'Show' instances, they're handled in the same automated way
below, just because the derived instances handle precedence (and thus insert parentheses in right
places) out of the box.

We should be able to use the same strategy for every type class @X@ when a @makeX@ function
(analogous to 'makeLift') is available.
-}

-- WARNING: DO NOT EXPORT THIS, IT HAS AN UNSOUND 'Lift' INSTANCE USED FOR INTERNAL PURPOSES.
-- | A wrapper that allows to provide an instance for a non-general class (e.g. 'Lift' or 'Show')
-- for any @f@ implementing a general class (e.g. 'GLift' or 'GShow').
newtype AG f a = AG (f a)

$(return [])  -- Stage restriction, see https://gitlab.haskell.org/ghc/ghc/issues/9813

-------------------- 'Show' / 'GShow'

instance GShow f => Show (AG f a) where
    showsPrec pr (AG a) = gshowsPrec pr a

instance GShow f => Show (Some f) where
    showsPrec pr (Some a) = ($(makeShowsPrec ''Some)) pr (Some (AG a))

instance GShow uni => Show (SomeTypeIn uni) where
    showsPrec pr (SomeTypeIn uni) = ($(makeShowsPrec ''SomeTypeIn)) pr (SomeTypeIn (AG uni))

instance GShow uni => Show (Kinded uni ta) where
    showsPrec pr (Kinded uni) = ($(makeShowsPrec ''Kinded)) pr (Kinded (AG uni))

instance GShow uni => GShow (Kinded uni) where gshowsPrec = showsPrec

instance (GShow uni, Closed uni, uni `Everywhere` Show) => GShow (ValueOf uni) where
    gshowsPrec = showsPrec
instance (GShow uni, Closed uni, uni `Everywhere` Show) => Show (ValueOf uni a) where
    showsPrec pr (ValueOf uni x) =
        bring (Proxy @Show) uni $ ($(makeShowsPrec ''ValueOf)) pr (ValueOf (AG uni) x)

-------------------- 'Eq' / 'GEq'

instance GEq f => Eq (Some f) where
    Some a1 == Some a2 = a1 `defaultEq` a2

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => GEq (ValueOf uni) where
    ValueOf uni1 x1 `geq` ValueOf uni2 x2 = do
        Refl <- uni1 `geq` uni2
        guard $ bring (Proxy @Eq) uni1 (x1 == x2)
        Just Refl

instance GEq uni => Eq (SomeTypeIn uni) where
    SomeTypeIn a1 == SomeTypeIn a2 = a1 `defaultEq` a2

instance (GEq uni, Closed uni, uni `Everywhere` Eq) => Eq (ValueOf uni a) where
    (==) = defaultEq

-------------------- 'NFData'

instance Closed uni => NFData (SomeTypeIn uni) where
    rnf (SomeTypeIn uni) = rnf $ encodeUni uni

instance (Closed uni, uni `Everywhere` NFData) => NFData (ValueOf uni a) where
    rnf (ValueOf uni x) = bring (Proxy @NFData) uni $ rnf x

instance (Closed uni, uni `Everywhere` NFData) => NFData (Some (ValueOf uni)) where
    rnf (Some s) = rnf s

-------------------- 'Hashable'

instance Closed uni => Hashable (SomeTypeIn uni) where
    hashWithSalt salt (SomeTypeIn uni) = hashWithSalt salt $ encodeUni uni

instance (Closed uni, uni `Everywhere` Hashable) => Hashable (ValueOf uni a) where
    hashWithSalt salt (ValueOf uni x) =
        bring (Proxy @Hashable) uni $ hashWithSalt salt (SomeTypeIn uni, x)

instance (Closed uni, uni `Everywhere` Hashable) => Hashable (Some (ValueOf uni)) where
    hashWithSalt salt (Some s) = hashWithSalt salt s
