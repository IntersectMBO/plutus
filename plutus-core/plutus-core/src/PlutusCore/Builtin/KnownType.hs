{-# LANGUAGE BlockArguments           #-}
{-# LANGUAGE ConstraintKinds          #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UndecidableInstances     #-}

{-# LANGUAGE StrictData               #-}

module PlutusCore.Builtin.KnownType
    ( BuiltinError
    , GEqL (..)
    , LoopBreaker (..)
    , KnownBuiltinTypeIn
    , KnownBuiltinType
    , BuiltinResult (..)
    , ReadKnownM
    , Spine (..)
    , HeadSpine (..)
    , headSpine
    , MonoHeadSpine
    , MakeKnownIn (..)
    , readKnownConstant
    , MakeKnown
    , ReadKnownIn (..)
    , ReadKnown
    , makeKnownOrFail
    , readKnownSelf
    ) where

import PlutusPrelude

import PlutusCore.Builtin.HasConstant
import PlutusCore.Builtin.Polymorphism
import PlutusCore.Builtin.Result
import PlutusCore.Core
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Result
import PlutusCore.Pretty

import Control.Monad.Except
import Data.Bifunctor
import Data.Either.Extras
import Data.Functor.Identity
import Data.Kind qualified as GHC
import Data.String
import GHC.Exts (inline, oneShot)
import GHC.TypeLits
import Prettyprinter
import Text.PrettyBy.Internal
import Universe

-- | A version of 'GEq' that fixes @a@ in place, which allows us to create an inlinable recursive
-- implementation of 'geqL'.
--
-- The way it works is that whenever there's recursion, we look up the recursive case in the current
-- context (i.e. the dictionary) instead of actually calling 'geqL' recursively (even though it's
-- gonna look like we do exactly that, because there's no way to distinguish between a recursive
-- call and a dictionary lookup as the two share the same name, although to help GHC choose a lookup
-- we sprinkle the perhaps unreliable 'LoopBreaker' in the 'DefaultUni' instance of this class).
--
-- Alligning things this way allows us to inline arbitrarily deep recursion for as long as types
-- keep being monomorphic.
--
-- For example, the 'MapData' builtin accepts a @[(Data, Data)]@ and with 'geqL' matching on all of
-- 'DefaultUniProtoList', 'DefaultUniProtoPair' and 'DefaultUniData' gets inlined in the denotation
-- of the builtin. For the 'Constr' builtin that resulted in a 4.3% speedup at the time this comment
-- was written.
type GEqL :: (GHC.Type -> GHC.Type) -> GHC.Type -> GHC.Constraint
class GEqL f a where
    geqL :: f (Esc a) -> f (Esc b) -> EvaluationResult (a :~: b)

-- | In @f = ... f ...@ where @f@ is a class method, how do you know if @f@ is going to be a
-- recursive call or a type class method call? If both type check, then you don't really know how
-- GHC is going to play it. So we add this data type to make sure that the RHS @f@ will have to
-- become a type class method call.
--
-- Can GHC turn that method call into a recursive one once type classes are resolved? Dunno, but at
-- least we've introduced an obstacle preventing GHC from immediately creating a non-inlinable
-- recursive definition.
newtype LoopBreaker uni a = LoopBreaker (uni a)

instance GEqL uni a => GEqL (LoopBreaker uni) a where
    geqL = coerce $ geqL @uni
    {-# INLINE geqL #-}

-- | A constraint for \"@a@ is a 'ReadKnownIn' and 'MakeKnownIn' by means of being included
-- in @uni@\".
type KnownBuiltinTypeIn uni val a =
    (HasConstantIn uni val, PrettyParens (SomeTypeIn uni), GEqL uni a, uni `HasTermLevel` a)

-- | A constraint for \"@a@ is a 'ReadKnownIn' and 'MakeKnownIn' by means of being included
-- in @UniOf term@\".
type KnownBuiltinType val a = KnownBuiltinTypeIn (UniOf val) val a

{- Note [Performance of ReadKnownIn and MakeKnownIn instances]
It's critically important that 'readKnown' runs in the concrete 'Either' rather than a general
'MonadError'. Changing from the latter to the former gave us a speedup of up to 19%, see
https://github.com/IntersectMBO/plutus/pull/4307

Replacing the @AsUnliftingError err, AsEvaluationFailure err@ constraints with the dedicated
'BuiltinError' data type gave us a speedup of up to 4%.

All the same considerations apply to 'makeKnown':
https://github.com/IntersectMBO/plutus/pull/4421

It's beneficial to inline 'readKnown' and 'makeKnown' not only because we use them directly over
concrete types once 'toBuiltinsRuntime' is inlined, but also because otherwise GHC compiles each of
them to two definitions (one calling the other) for some reason.
So always add an @INLINE@ pragma to all definitions of 'makeKnown' and 'readKnown' unless you have
a specific reason not to.

Neither 'readKnown' nor 'makeKnown' should appear in the generated Core for builtins. In most cases
they would slow builtins down, but even if a 'readKnown' only throws an error, it still makes sense
to keep it out of Core just not to trigger an investigation on whether it's fine that a call to
'readKnown' is not inlined.

Some 'readKnown' implementations require inserting a call to 'oneShot'. E.g. if 'oneShot' is not
used in 'readKnownConstant' then 'GHC pulls @gshow uniExp@ out of the 'Nothing' branch, thus
allocating a thunk of type 'String' that is completely redundant whenever there's no error,
which is the majority of cases. And putting 'oneShot' as the outermost call results in
worse Core.

Any change to an instance of 'ReadKnownIn' or 'MakeKnownIn', even completely trivial, requires
looking into the generated Core, since compilation of these instances is extremely brittle
optimization-wise.

Things to watch out for are unnecessary sharing (for example, a @let@ appearing outside of a @case@
allocates a thunk and if that thunk is not referenced inside of one of the branches, then it's
wasteful, especially when it's not referenced in the most commonly chosen branch) and type class
methods not being extracted from the dictionary and used directly instead (i.e. if you see
multiple @pure@ and @>>=@ in the code, that's not good). Note that neither @let@ nor @>>=@ are bad
in general, we certainly do need to allocate thunks occasionally, it's just that when it comes to
builtins this is rarely the case as most of the time we want aggressive inlining and specialization
and the "just compute the damn thing" behavior.
-}

{- Note [Unlifting terminology]
This function:

    f :: Integer -> CkValue DefaultUni fun
    f = VCon . Some . ValueOf DefaultUniInteger

lifts an 'Integer' to 'CkValue'. Unlifting is the opposite:

    g :: CkValue DefaultUni fun -> Maybe Integer
    g (VCon (Some (ValueOf uni x))) = case uni of
        DefaultUniInteger -> Just x
        _                 -> Nothing

The following usages of the "unlift" term are grammatical:

1. unlift a 'CkValue' to 'Integer'
2. unlift to 'Integer'
3. unlift a 'CkValue' as an 'Integer'
4. unlift from the 'VCon' constructor (or just 'VCon') to 'Integer'

We call the integer that @g@ returns "the unlifted integer".
-}

{- Note [Unlifting a term as a value of a built-in type]
See Note [Unlifting terminology] first.

It's trivial to unlift a term to a monomorphic built-in type like 'Integer': just check that the
term is a constant, extract the type tag and check it for equality with the type tag of 'Integer'.

Things work the same way for a fully monomorphized polymorphic type, i.e. @(Integer, Bool@) is not
any different from just 'Integer' unlifting-wise.

(TODO: the following explanation needs to be improved, there's PLT-338 for that)

However there's no sensible way of unlifting to, say, @[a]@ where @a@ in not a built-in type. So
let's say we instantiated @a@ to an @Opaque val rep@ like we do for polymorphic functions that don't
deal with polymorphic built-in types (e.g. @id@, @ifThenElse@ etc). That would mean we'd need to
write a function from a @[a]@ for some arbitrary built-in @a@ to @[Opaque val a]@. Which is really
easy to do: it's just @map makeKnown@. But the problem is, unlifting is supposed to be cheap and
that @map@ is O(n), so for example 'MkCons' would become an O(n) operation making perfectly linear
algorithms quadratic. See https://github.com/IntersectMBO/plutus/pull/4215 for how that would
look like.

So the problem is that we can't convert in O(1) time a @[a]@ coming from a constant of
statically-unknown type (that @a@ is existential) to @[a']@ where @a'@ is known statically.
Thus it's impossible to instantiate @a@ in Haskell's

    nullList :: [a] -> Bool

so that there's a 'TypeScheme' for this function.

One non-solution would be to instantiate @a@, then recurse on the type, construct a new function
that defers to the original @nullList@ but wraps its argument in a specific way (more on that below)
making it possible to assign a 'TypeScheme' to the resulting function. Astonishingly enough, that
could actually work and if we ever write a paper on builtins, we should mention that example, but:

1. such a trick requires a generic machinery that knows how to check that the head of the builtin
   application is a particular built-in type. We used to have that, but it was just way too slow
2. that would only work for functions that don't care about @a@ at all. But for example when
   elaborating @cons :: a -> [a] -> [a]@ as a Plutus builtin we need to unlift both the arguments
   and check that their @a@s are equal
   (See Note [Representable built-in functions over polymorphic built-in types])
   and it's either way too complex or even impossible to do that automatically within some generic
   machinery

So what we do is we simply require the user to write

    nullList :: SomeConstant uni [a] -> Bool

and unlift to @[a]@ manually within the definition of the builtin. This works, because the
existential @a@ never escapes the definition of the builtin. I.e. it's fine to unpack an existential
and use it immediately without ever exposing the existential parts to the outside and it's not fine
to try to return a value having an existential inside of it, which is what unlifting to @[a]@ would
amount to.

Could we somehow align the unlifting machinery so that it does not construct values of particular
types, but rather feeds them to a continuation or something, so that the existential parts never
try to escape? Maybe, but see point 2 from the above, we do want to get our hands on the particular
universes sometimes and point 1 prevents us from doing that generically, so it doesn't seem like
we could do that within some automated machinery.

Overall, asking the user to manually unlift a @SomeConstant uni [a]@ is just always going to be
faster than any kind of fancy encoding.
-}

{- Note [Alignment of ReadKnownIn and MakeKnownIn]
We keep 'ReadKnownIn' and 'MakeKnownIn' separate, because values of some types can only be lifted
and not unlifted, for example 'EvaluationResult' and 'Emitter' can't appear in argument position.

'KnownTypeAst' is not a superclass of ReadKnownIn and MakeKnownIn. This is due to the fact that
polymorphic built-in types are only liftable/unliftable when they're fully monomorphized, while
'toTypeAst' works for polymorphic built-in types that have type variables in them, and so the
constraints are completely different in the two cases and we keep the two concepts apart
(there doesn't seem to be any cons to that).
-}

{- Note [Allowed unlifting and lifting]
Read Note [Alignment of ReadKnownIn and MakeKnownIn] first.

The following classes of Haskell types represent Plutus types:

1. monomorphic built-in types such as @Bool@
   (assuming @Bool@ is in the universe)
2. polymorphic built-in types such as @(a, b)@ for any @a@ and @b@ representing Plutus types
   (assuming @(,)@ is in the universe)
3. @Opaque val rep@ for any @rep@ representing a Plutus type
4. @SomeConstant uni rep@ for any @rep@ representing a Plutus type
5. @Emitter a@ for any @a@ representing a Plutus type
6. @EvaluationResult a@ for any @a@ representing a Plutus type
7. 'TyVarRep', 'TyAppRep', 'TyForallRep' and all similar types mirroring constructors of @Type@
8. @a -> b@ for any @a@ and @b@ representing Plutus types (mirrors 'TyFun')
9. anything else that has a 'KnownTypeAst' instance, for example we express the
   @KnownTypeAst DefaultUni Int@ instance in terms of the @KnownType DefaultUni Integer@
   one

Unlifting is allowed to the following classes of types:

1. monomorphic built-in types such as @Bool@
2. monomorphized polymorphic built-in types such as @(Integer, Text)@
3. @Opaque val rep@ for @rep@ representing a Plutus type
4. @SomeConstant uni rep@ for @rep@ representing a Plutus type
5. anything else that implements 'ReadKnownIn', for example we express the
   @ReadKnownIn DefaultUni term Int@ instance in terms of the @ReadKnownIn DefaultUni term Integer@
   one, and for another example define an instance for 'Void' in tests

Lifting is allowed to the following classes of types:

1. monomorphic built-in types such as @Bool@
2. monomorphized polymorphic built-in types such as @(Integer, Text)@
3. @Opaque val rep@ for @rep@ representing a Plutus type
4. @SomeConstant uni rep@ for @rep@ representing a Plutus type
5. @Emitter a@ for any @a@ that lifting is allowed to
6. @EvaluationResult a@ for any @a@ that lifting is allowed to
7. anything else that implements 'MakeKnownIn', for example we express the
   @MakeKnownIn DefaultUni term Int@ instance in terms of the @MakeKnownIn DefaultUni term Integer@
   one, and for another example define an instance for 'Void' in tests
-}

typeMismatchError
    :: PrettyParens (SomeTypeIn uni)
    => uni (Esc a)
    -> uni (Esc b)
    -> UnliftingEvaluationError
typeMismatchError uniExp uniAct =
    MkUnliftingEvaluationError . StructuralError . fromString $ concat
        [ "Type mismatch: "
        , "expected: " ++ displayBy botRenderContext (SomeTypeIn uniExp)
        , "; actual: " ++ displayBy botRenderContext (SomeTypeIn uniAct)
        ]
-- See Note [INLINE and OPAQUE on error-related definitions].
{-# OPAQUE typeMismatchError #-}

-- Normally it's a good idea for an exported abstraction not to be a type synonym, since a @newtype@
-- is cheap, looks good in error messages and clearly emphasize an abstraction barrier. However we
-- make 'ReadKnownM' a type synonym for convenience: that way we don't need to derive all the
-- instances (and add new ones whenever we need them), wrap and unwrap all the time (including in
-- user code), which can be non-trivial for such performance-sensitive code (see e.g. '(#.)' and
-- 'coerceArg') and there is no abstraction barrier anyway.
-- | The monad that 'readKnown' runs in.
type ReadKnownM = Either BuiltinError

-- See Note [Unlifting a term as a value of a built-in type].
-- | Convert a constant embedded into a PLC term to the corresponding Haskell value.
readKnownConstant :: forall val a. KnownBuiltinType val a => val -> ReadKnownM a
-- See Note [Performance of ReadKnownIn and MakeKnownIn instances]
readKnownConstant val = asConstant val >>= oneShot \case
    Some (ValueOf uniAct x) -> do
        let uniExp = knownUni @_ @(UniOf val) @a
        -- 'geq' matches on its first argument first, so we make the type tag that will be known
        -- statically (because this function will be inlined) go first in order for GHC to
        -- optimize some of the matching away.
        case uniExp `geqL` uniAct of
            EvaluationSuccess Refl -> pure x
            EvaluationFailure ->
                throwError . BuiltinUnliftingEvaluationError $ typeMismatchError uniExp uniAct
{-# INLINE readKnownConstant #-}

-- | A non-empty spine. Isomorphic to 'NonEmpty', except is strict and is defined as a single
-- recursive data type.
data Spine a
    = SpineLast a
    | SpineCons a (Spine a)
    deriving stock (Show, Eq, Foldable, Functor)

-- | The head-spine form of an iterated application. Provides O(1) access to the head of the
-- application. @NonEmpty a ~ HeadSpine a a@, except is strict and the no-spine case is made a separate
-- constructor for performance reasons (it only takes a single pattern match to access the head when
-- there's no spine this way, while otherwise we'd also need to match on the spine to ensure that
-- it's empty -- and the no-spine case is by far the most common one, hence we want to optimize it).
--
-- Used in built-in functions returning function applications such as 'CaseList'.
data HeadSpine a b
    = HeadOnly a
    | HeadSpine a (Spine b)
    deriving stock (Show, Eq, Functor)

-- | @HeadSpine@ but the type of head and spine is same
type MonoHeadSpine a = HeadSpine a a

instance Bifunctor HeadSpine where
  bimap headF _ (HeadOnly a)         = HeadOnly $ headF a
  bimap headF spineF (HeadSpine a b) = HeadSpine (headF a) (spineF <$> b)

-- | Construct @HeadSpine@ from head and list.
headSpine :: a -> [b] -> HeadSpine a b
headSpine h [] = HeadOnly h
headSpine h (x:xs) =
  -- It's critical to use 'foldr' here, so that deforestation kicks in.
  -- See Note [Definition of foldl'] in "GHC.List" and related Notes around for an explanation
  -- of the trick.
  HeadSpine h $ foldr (\x2 r x1 -> SpineCons x1 $ r x2) SpineLast xs x
{-# INLINE headSpine #-}

-- |
--
-- >>> import Text.Pretty
-- >>> pretty (SpineCons 'a' $ SpineLast 'b')
-- [a, b]
instance Pretty a => Pretty (Spine a) where pretty = pretty . map Identity . toList
instance PrettyBy config a => DefaultPrettyBy config (Spine a)
deriving via PrettyCommon (Spine a)
    instance PrettyDefaultBy config (Spine a) => PrettyBy config (Spine a)

-- |
--
-- >>> import Text.Pretty
-- >>> pretty (HeadOnly 'z')
-- z
-- >>> pretty (HeadSpine 'f' (SpineCons 'x' $ SpineLast 'y'))
-- f `applyN` [x, y]
instance (Pretty a, Pretty b) => Pretty (HeadSpine a b) where
    pretty (HeadOnly x)     = pretty x
    pretty (HeadSpine f xs) = pretty f <+> "`applyN`" <+> pretty xs
instance (PrettyBy config a, PrettyBy config b) => DefaultPrettyBy config (HeadSpine a b)
deriving via PrettyCommon (HeadSpine a b)
    instance PrettyDefaultBy config (HeadSpine a b) => PrettyBy config (HeadSpine a b)

-- See Note [Performance of ReadKnownIn and MakeKnownIn instances].
class uni ~ UniOf val => MakeKnownIn uni val a where
    -- | Convert a Haskell value to the corresponding PLC value.
    -- The inverse of 'readKnown'.
    makeKnown :: a -> BuiltinResult val
    default makeKnown :: KnownBuiltinType val a => a -> BuiltinResult val
    -- Everything on evaluation path has to be strict in production, so in theory we don't need to
    -- force anything here. In practice however all kinds of weird things happen in tests and @val@
    -- can be non-strict enough to cause trouble here, so we're forcing the argument. Looking at the
    -- generated Core, the forcing amounts to pulling a @case@ out of the 'fromConstant' call,
    -- which doesn't affect the overall cost and benchmarking results suggest the same.
    --
    -- Note that the value is only forced to WHNF, so care must be taken to ensure that every value
    -- of a type from the universe gets forced to NF whenever it's forced to WHNF.
    makeKnown x = pure . fromValue $! x
    {-# INLINE makeKnown #-}

type MakeKnown val = MakeKnownIn (UniOf val) val

-- See Note [Performance of ReadKnownIn and MakeKnownIn instances].
class uni ~ UniOf val => ReadKnownIn uni val a where
    -- | Convert a PLC value to the corresponding Haskell value.
    -- The inverse of 'makeKnown'.
    readKnown :: val -> ReadKnownM a
    default readKnown :: KnownBuiltinType val a => val -> ReadKnownM a
    -- If 'inline' is not used, proper inlining does not happen for whatever reason.
    readKnown = inline readKnownConstant
    {-# INLINE readKnown #-}

type ReadKnown val = ReadKnownIn (UniOf val) val

-- | Same as 'makeKnown', but allows for neither emitting nor storing the cause of a failure.
makeKnownOrFail :: MakeKnownIn uni val a => a -> EvaluationResult val
makeKnownOrFail x = case makeKnown x of
    BuiltinSuccess val           -> EvaluationSuccess val
    BuiltinSuccessWithLogs _ val -> EvaluationSuccess val
    BuiltinFailure _ _           -> EvaluationFailure
{-# INLINE makeKnownOrFail #-}

-- | Same as 'readKnown', but the cause of a potential failure is the provided term itself.
readKnownSelf
    :: (ReadKnown val a, BuiltinErrorToEvaluationError structural operational)
    => val -> Either (ErrorWithCause (EvaluationError structural operational) val) a
readKnownSelf val =
    fromRightM (flip throwErrorWithCause val . builtinErrorToEvaluationError) $ readKnown val
{-# INLINE readKnownSelf #-}

instance MakeKnownIn uni val a => MakeKnownIn uni val (BuiltinResult a) where
    makeKnown res = res >>= makeKnown
    {-# INLINE makeKnown #-}

-- Catching 'EvaluationFailure' here would allow *not* to short-circuit when 'readKnown' fails
-- to read a Haskell value of type @a@. Instead, in the denotation of the builtin function
-- the programmer would be given an explicit 'EvaluationResult' value to handle, which means
-- that when this value is 'EvaluationFailure', a PLC 'Error' was caught.
-- I.e. it would essentially allow us to catch errors and handle them in a programmable way.
-- We forbid this, because it complicates code and isn't supported by evaluation engines anyway.
instance
        ( TypeError ('Text "‘BuiltinResult’ cannot appear in the type of an argument")
        , uni ~ UniOf val
        ) => ReadKnownIn uni val (BuiltinResult a) where
    readKnown _ = throwError underTypeError
    {-# INLINE readKnown #-}

instance
        ( TypeError ('Text "Use ‘BuiltinResult’ instead of ‘EvaluationResult’")
        , uni ~ UniOf val
        ) => MakeKnownIn uni val (EvaluationResult a) where
    makeKnown _ = throwError underTypeError
    {-# INLINE makeKnown #-}

instance
        ( TypeError ('Text "Use ‘BuiltinResult’ instead of ‘EvaluationResult’")
        , uni ~ UniOf val
        ) => ReadKnownIn uni val (EvaluationResult a) where
    readKnown _ = throwError underTypeError
    {-# INLINE readKnown #-}

instance HasConstantIn uni val => MakeKnownIn uni val (SomeConstant uni rep) where
    makeKnown = coerceArg $ pure . fromConstant
    {-# INLINE makeKnown #-}

instance HasConstantIn uni val => ReadKnownIn uni val (SomeConstant uni rep) where
    readKnown = fmap SomeConstant #. asConstant
    {-# INLINE readKnown #-}

instance uni ~ UniOf val => MakeKnownIn uni val (Opaque val rep) where
    makeKnown = coerceArg pure
    {-# INLINE makeKnown #-}

instance uni ~ UniOf val => ReadKnownIn uni val (Opaque val rep) where
    readKnown = coerceArg pure
    {-# INLINE readKnown #-}
