{-# LANGUAGE BlockArguments          #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DefaultSignatures       #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE KindSignatures          #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE OverloadedStrings       #-}
{-# LANGUAGE QuantifiedConstraints   #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module PlutusCore.Builtin.KnownType
    ( KnownBuiltinTypeIn
    , KnownBuiltinType
    , readKnownConstant
    , KnownTypeIn (..)
    , KnownType
    , TestTypesFromTheUniverseAreAllKnown
    , readKnownSelf
    , makeKnownOrFail
    ) where

import PlutusCore.Builtin.Emitter
import PlutusCore.Builtin.HasConstant
import PlutusCore.Builtin.KnownTypeAst
import PlutusCore.Builtin.Polymorphism
import PlutusCore.Core
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Evaluation.Result

import Control.Monad.Except
import Data.Coerce
import Data.Kind qualified as GHC (Type)
import Data.String
import Data.Text (Text)
import GHC.Exts (inline, oneShot)
import Universe

-- | A constraint for \"@a@ is a 'KnownType' by means of being included in @uni@\".
type KnownBuiltinTypeIn uni val a = (HasConstantIn uni val, GShow uni, GEq uni, uni `Contains` a)

-- | A constraint for \"@a@ is a 'KnownType' by means of being included in @UniOf term@\".
type KnownBuiltinType val a = KnownBuiltinTypeIn (UniOf val) val a

{- Note [Performance of KnownTypeIn instances]
It's critically important that 'readKnown' runs in the concrete 'Either' rather than a general
'MonadError'. Changing from the latter to the former gave us a speedup of up to 19%, see
https://github.com/input-output-hk/plutus/pull/4307

The same does not apply to 'makeKnown' however and so we keep 'MonadError' there, see
https://github.com/input-output-hk/plutus/pull/4308
Although there's a different kind of inlining that helps in case of 'makeKnown', see the first
commit and the first comment of https://github.com/input-output-hk/plutus/pull/4251
We don't have it merged currently though, because there's a hope for a better solution.

Even though we don't use 'makeKnown' and 'readKnown' directly over concrete types, it's still
beneficial to inline them, because otherwise GHC compiles each of them to two definitions
(one calling the other) for some reason. So always add an @INLINE@ pragma to all definitions
of 'makeKnown' and 'readKnown' unless you have a specific reason not to.

Similarly, we inline implementations of 'toTypeAst' just to get tidier Core.

Some 'readKnown' implementations require inserting a call to 'oneShot'. E.g. if 'oneShot' is not
used in 'readKnownConstant' then 'GHC pulls @gshow uniExp@ out of the 'Nothing' branch, thus
allocating a thunk of type 'String' that is completely redundant whenever there's no error,
which is the majority of cases. And putting 'oneShot' as the outermost call results in
worse Core.

Any change to an instance of 'KnownTypeIn', even completely trivial, requires looking into the
generated Core, since compilation of these instances is extremely brittle optimization-wise.

Things to watch out for are unnecessary sharing (for example, a @let@ appearing outside of a @case@
allocates a thunk and if that thunk is not referenced inside of one of the branches, then it's
wasteful, especially when it's not referenced in the most commonly chosen branch) and type class
methods not being extracted from the dictionary and used directly instead (i.e. if you see
multiple @pure@ and @>>=@ in the code, that's not good). Note that neither @let@ nor @>>=@ are bad
in general, we certainly do need to allocate thunks occasionally, it's just that when it comes to
builtins this is rarely the case as most of the time we want aggressive inlining and specialization
and the "just compute the damn thing" behavior.
-}

{- Note [Unlifting values of built-in types]
It's trivial to unlift from a term a value of a monomorphic type like 'Integer': just check that
the term is a constant, extract the type tag and check it for equality with the type tag of
'Integer'.

Things work the same way for a fully monomorphized polymorphic type, i.e. @(Integer, Bool@) is not
any different from just 'Integer' unlifting-wise.

However there's no sensible way of unlifting a value of, say, @[a]@ where @a@ in not a built-in
type. So let's say we instantiated @a@ to an @Opaque val rep@ like we do for polymorphic functions
that don't deal with polymorphic built-in types (e.g. `id`, `ifThenElse` etc). That would mean we'd
need to write a function from a @[a]@ for some arbitrary built-in @a@ to @[Opaque val a]@. Which
is really easy to do: it's just @map makeKnown@. But the problem is, unlifting is supposed to be
cheap and that @map@ is O(n), so for example 'MkCons' would become an O(n) operation making
perfectly linear algorithms quadratic. See https://github.com/input-output-hk/plutus/pull/4215 for
how that would look like.

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

    nullList :: Opaque val [a] -> Bool

and unlift a @[a]@ manually within the definition of the builtin. This works, because the
existential @a@ never escapes the definition of the builtin. I.e. it's fine to unpack an existential
and use it immediately without ever exposing the existential parts to the outside and it's not fine
to try to return a value having an existential inside of it, which is what unlifting of @[a]@ would
amount to.

Could we somehow align the unlifting machinery so that it does not construct values of particular
types, but rather feeds them to a continuation or something, so that the existential parts never
try to escape? Maybe, but see point 2 from the above, we do want to get our hands on the particular
universes sometimes and point 1 prevents us from doing that generically, so it doesn't seem like
we could do that within some automated machinery.

Overall, asking the user to manually unlift from @Opaque val [a]@ is just always going to be
faster than any kind of fancy encoding.
-}

-- See Note [Unlifting values of built-in types].
-- | Convert a constant embedded into a PLC term to the corresponding Haskell value.
readKnownConstant
    :: forall val a err cause. (AsUnliftingError err, KnownBuiltinType val a)
    => Maybe cause -> val -> Either (ErrorWithCause err cause) a
-- See Note [Performance of KnownTypeIn instances].
readKnownConstant mayCause val = asConstant mayCause val >>= oneShot \case
    Some (ValueOf uniAct x) -> do
        let uniExp = knownUni @_ @(UniOf val) @a
        -- 'geq' matches on its first argument first, so we make the type tag that will be known
        -- statically go first in order for GHC to optimize some of the matching away.
        case uniExp `geq` uniAct of
            Just Refl -> pure x
            Nothing   -> do
                let err = fromString $ concat
                        [ "Type mismatch: "
                        , "expected: " ++ gshow uniExp
                        , "; actual: " ++ gshow uniAct
                        ]
                throwingWithCause _UnliftingError err mayCause
{-# INLINE readKnownConstant #-}

-- See Note [Performance of KnownTypeIn instances].
-- We use @default@ for providing instances for built-in types instead of @DerivingVia@, because
-- the latter breaks on @m term@ (and for brevity).
-- | Haskell types known to exist on the PLC side.
-- Both the methods take a @Maybe cause@ argument to report the cause of a potential failure.
-- @cause@ is different to @term@ to support evaluators that distinguish between terms and values
-- (@makeKnown@ normally constructs a value, but it's convenient to report the cause of a failure
-- as a term). Note that an evaluator might require the cause to be computed lazily for best
-- performance on the happy path and @Maybe@ ensures that even if we somehow force the argument,
-- the cause stored in it is not forced due to @Maybe@ being a lazy data type.
-- Note that 'KnownTypeAst' is not a superclass of 'KnownTypeIn'. This is due to the fact that
-- polymorphic built-in types are only liftable/unliftable when they're fully monomorphized, while
-- 'toTypeAst' works for polymorphic built-in types that have type variables in them, and so the
-- constraints are completely different in the two cases and we keep the two classes apart
-- (there doesn't seem to be any cons to that).
class uni ~ UniOf val => KnownTypeIn uni val a where
    -- | Convert a Haskell value to the corresponding PLC val.
    -- The inverse of 'readKnown'.
    makeKnown
        :: ( MonadError (ErrorWithCause err cause) m, AsEvaluationFailure err
           )
        => (Text -> m ()) -> Maybe cause -> a -> m val
    default makeKnown
        :: ( MonadError (ErrorWithCause err cause) m
           , KnownBuiltinType val a
           )
        => (Text -> m ()) -> Maybe cause -> a -> m val
    -- Forcing the value to avoid space leaks. Note that the value is only forced to WHNF,
    -- so care must be taken to ensure that every value of a type from the universe gets forced
    -- to NF whenever it's forced to WHNF.
    makeKnown _ _ x = pure . fromConstant . someValue $! x
    {-# INLINE makeKnown #-}

    -- | Convert a PLC val to the corresponding Haskell value.
    -- The inverse of 'makeKnown'.
    readKnown
        :: ( AsUnliftingError err, AsEvaluationFailure err
           )
        => Maybe cause -> val -> Either (ErrorWithCause err cause) a
    default readKnown
        :: ( AsUnliftingError err
           , KnownBuiltinType val a
           )
        => Maybe cause -> val -> Either (ErrorWithCause err cause) a
    -- If 'inline' is not used, proper inlining does not happen for whatever reason.
    readKnown = inline readKnownConstant
    {-# INLINE readKnown #-}

-- | Haskell types known to exist on the PLC side. See 'KnownTypeIn'.
type KnownType val a = (KnownTypeAst (UniOf val) a, KnownTypeIn (UniOf val) val a)

-- | Same as 'readKnown', but the cause of a potential failure is the provided term itself.
readKnownSelf
    :: ( KnownType val a
       , AsUnliftingError err, AsEvaluationFailure err
       )
    => val -> Either (ErrorWithCause err val) a
readKnownSelf val = readKnown (Just val) val

-- | For providing a 'KnownTypeIn' instance for a built-in type it's enough for that type to satisfy
-- 'KnownBuiltinTypeIn', hence the definition.
class    (forall val. KnownBuiltinTypeIn uni val a => KnownTypeIn uni val a) =>
    ImplementedKnownBuiltinTypeIn uni a
instance (forall val. KnownBuiltinTypeIn uni val a => KnownTypeIn uni val a) =>
    ImplementedKnownBuiltinTypeIn uni a

-- | An instance of this class not having any constraints ensures that every type
-- (according to 'Everywhere') from the universe has a 'KnownTypeIn' instance.
class uni `Everywhere` ImplementedKnownBuiltinTypeIn uni => TestTypesFromTheUniverseAreAllKnown uni

-- | A transformer for fitting a monad not carrying the cause of a failure into 'makeKnown'.
newtype NoCauseT (val :: GHC.Type) m a = NoCauseT
    { unNoCauseT :: m a
    } deriving newtype (Functor, Applicative, Monad)

instance (MonadError err m, AsEvaluationFailure err) =>
            MonadError (ErrorWithCause err val) (NoCauseT val m) where
    throwError _ = NoCauseT $ throwError evaluationFailure
    NoCauseT a `catchError` h =
        NoCauseT $ a `catchError` \err ->
            unNoCauseT . h $ ErrorWithCause err Nothing

-- | Same as 'makeKnown', but allows for neither emitting nor storing the cause of a failure.
-- For example the monad can be simply 'EvaluationResult'.
makeKnownOrFail :: (KnownType val a, MonadError err m, AsEvaluationFailure err) => a -> m val
makeKnownOrFail = unNoCauseT . makeKnown (\_ -> pure ()) Nothing

instance KnownTypeIn uni val a => KnownTypeIn uni val (EvaluationResult a) where
    makeKnown _    mayCause EvaluationFailure     = throwingWithCause _EvaluationFailure () mayCause
    makeKnown emit mayCause (EvaluationSuccess x) = makeKnown emit mayCause x
    {-# INLINE makeKnown #-}

    -- Catching 'EvaluationFailure' here would allow *not* to short-circuit when 'readKnown' fails
    -- to read a Haskell value of type @a@. Instead, in the denotation of the builtin function
    -- the programmer would be given an explicit 'EvaluationResult' value to handle, which means
    -- that when this value is 'EvaluationFailure', a PLC 'Error' was caught.
    -- I.e. it would essentially allow us to catch errors and handle them in a programmable way.
    -- We forbid this, because it complicates code and isn't supported by evaluation engines anyway.
    readKnown mayCause _ =
        throwingWithCause _UnliftingError "Error catching is not supported" mayCause
    {-# INLINE readKnown #-}

instance KnownTypeIn uni val a => KnownTypeIn uni val (Emitter a) where
    makeKnown emit mayCause (Emitter k) = k emit >>= makeKnown emit mayCause
    {-# INLINE makeKnown #-}

    -- TODO: we really should tear 'KnownType' apart into two separate type classes.
    readKnown mayCause _ = throwingWithCause _UnliftingError "Can't unlift an 'Emitter'" mayCause
    {-# INLINE readKnown #-}

instance HasConstantIn uni val => KnownTypeIn uni val (SomeConstant uni rep) where
    makeKnown _ _ = coerceArg $ pure . fromConstant
    {-# INLINE makeKnown #-}

    readKnown = coerceVia (\asC mayCause -> fmap SomeConstant . asC mayCause) asConstant
    {-# INLINE readKnown #-}

instance uni ~ UniOf val => KnownTypeIn uni val (Opaque val rep) where
    makeKnown _ _ = coerceArg pure  -- A faster @pure . Opaque@.
    {-# INLINE makeKnown #-}

    readKnown _ = coerceArg pure  -- A faster @pure . Opaque@.
    {-# INLINE readKnown #-}

-- Utils

-- | Coerce the second argument to the result type of the first one. The motivation for this
-- function is that it's often more annoying to explicitly specify a target type for 'coerce' than
-- to constructor an explicit coercion function, so this combinator can be used in cases like that.
-- Plus the code reads better, as it becomes clear what and where gets wrapped/unwrapped.
coerceVia :: Coercible a b => (a -> b) -> a -> b
coerceVia _ = coerce
{-# INLINE coerceVia #-}

-- | Same as @\f -> f . coerce@, but does not create any closures and so is completely free.
coerceArg :: Coercible a b => (a -> r) -> b -> r
coerceArg = coerce
{-# INLINE coerceArg #-}
