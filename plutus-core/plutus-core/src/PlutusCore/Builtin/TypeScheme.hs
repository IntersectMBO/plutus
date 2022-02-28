-- | This module assigns types to built-ins.
-- See the @plutus/plutus-core/docs/Constant application.md@
-- article for how this emerged.

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

{-# LANGUAGE StrictData       #-}

module PlutusCore.Builtin.TypeScheme
    ( TypeScheme (..)
    , argProxy
    , FoldArgs
    , FoldArgsEx
    , typeSchemeToType
    ) where

import PlutusCore.Builtin.KnownKind
import PlutusCore.Builtin.KnownType
import PlutusCore.Builtin.KnownTypeAst
import PlutusCore.Core
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExMemory
import PlutusCore.Evaluation.Machine.Exception
import PlutusCore.Name

import Data.Kind qualified as GHC (Type)
import Data.Proxy
import Data.Text qualified as Text
import GHC.TypeLits

infixr 9 `TypeSchemeArrow`

{- Note [KnownType in TypeSchemeArrow]
There's a @KnownType val arg@ constrained packed in the 'TypeSchemeArrow' constructor. We're not
supposed to have it there, it really should be enough to have 'KnownTypeAst', because 'readKnown'
is inlined as an explicit argument. Unfortunately, in the @Generators@ tests we use 'TypeScheme'
for generation of arbitrary arguments of builtins and that requires 'makeKnown', which makes us
have the whole 'KnownType' in 'TypeSchemeArrow', which also retains the unspecialized 'readKnown',
which pollutes Core quite a bit and in particular makes it unclear whether the whole 'HasConstant'
business is inlined away or not.

There are two things that need to be done:

1. 'KnownTypeIn' needs to be split into two classes. Unfortunately, it's not as easy as it may seem:
   we did it in https://github.com/input-output-hk/plutus/pull/4420 and it introduced a 2-5%
   slowdown
2. the @Generators@ tests need to do something else. Explicitly constraining @args@ outside of
   'TypeScheme' sounds like a promising strategy. Maybe we could just delete those tests altogether

However it's also worth considering untangling 'RuntimeScheme' from 'TypeScheme' and generating the
two in parallel, so that we only need to optimize the former. Then we will be able to afford having
any kind of nonsense in 'TypeScheme'. Another reason for that would be the fact that Core output
has 'typeSchemeToRuntimeScheme' all over the place as it can't be inlined due to being a recursive
function, which we can't turn into an inlinable class method, because the indices of 'TypeScheme'
don't reflect its structure due to the 'TypeSchemeAll' constructor not being reflected at the type
level in any way. It's unlikely that having those 'typeSchemeToRuntimeScheme' has any impact on
performance, because they're only evaluated once during initialization, but it certainly has impact
on readability of the Core output.
-}

-- See Note [KnownType in TypeSchemeArrow].
-- | Type schemes of primitive operations.
-- @args@ is a list of types of arguments, @res@ is the resulting type.
-- E.g. @Text -> Bool -> Integer@ is encoded as @TypeScheme val [Text, Bool] Integer@.
data TypeScheme val (args :: [GHC.Type]) res where
    TypeSchemeResult
        :: KnownType val res
        => TypeScheme val '[] res
    TypeSchemeArrow
        :: KnownType val arg
           -- Inlining 'readKnown' here, so that it gets specialized and optimized properly.
        => (forall cause. Maybe cause -> val -> Either (ErrorWithCause ReadKnownError cause) arg)
        -> TypeScheme val args res
        -> TypeScheme val (arg ': args) res
    TypeSchemeAll
        :: (KnownSymbol text, KnownNat uniq, KnownKind kind)
        => Proxy '(text, uniq, kind)
        -> TypeScheme val args res
        -> TypeScheme val args res

argProxy :: TypeScheme val (arg ': args) res -> Proxy arg
argProxy _ = Proxy

-- | Turn a list of Haskell types @args@ into a functional type ending in @res@.
--
-- >>> :set -XDataKinds
-- >>> :kind! FoldArgs [Text, Bool] Integer
-- FoldArgs [Text, Bool] Integer :: *
-- = Text -> Bool -> Integer
type family FoldArgs args res where
    FoldArgs '[]           res = res
    FoldArgs (arg ': args) res = arg -> FoldArgs args res

-- | Calculates the parameters of the costing function for a builtin.
type family FoldArgsEx args where
    FoldArgsEx '[]           = ExBudget
    FoldArgsEx (arg ': args) = ExMemory -> FoldArgsEx args

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
-- Basically, a map from the PHOAS representation to the FOAS one.
typeSchemeToType :: TypeScheme val args res -> Type TyName (UniOf val) ()
typeSchemeToType sch@TypeSchemeResult       = toTypeAst sch
typeSchemeToType sch@(TypeSchemeArrow _ schB) =
    TyFun () (toTypeAst $ argProxy sch) $ typeSchemeToType schB
typeSchemeToType (TypeSchemeAll proxy schK) = case proxy of
    (_ :: Proxy '(text, uniq, kind)) ->
        let text = Text.pack $ symbolVal @text Proxy
            uniq = fromIntegral $ natVal @uniq Proxy
            a    = TyName $ Name text $ Unique uniq
        in TyForall () a (demoteKind $ knownKind @kind) $ typeSchemeToType schK

{- Note [Pattern matching on built-in types]
At the moment we really only support direct pattern matching on enumeration types: 'Void', 'Unit',
'Bool' etc. This is because the denotation of a builtin cannot construct general terms (as opposed
to constants), only juggle the ones that were provided as arguments without changing them.
So e.g. if we wanted to add the following data type:

    newtype AnInt = AnInt Int

as a built-in type, we wouldn't be able to add the following function as its pattern matcher:

    matchAnInt :: AnInt -> (Int -> r) -> r
    matchAnInt (AnInt i) f = f i

because currently we cannot express the @f i@ part using the builtins machinery as that would
require applying an arbitrary Plutus Core function in the denotation of a builtin, which would
allow us to return arbitrary terms from the builtin application machinery, which is something
that we originally had, but decided to abandon due to performance concerns.

But it's still possible to have @AnInt@ as a built-in type, it's just that instead of trying to
make its pattern matcher into a builtin we can have the following builtin:

    anIntToInt :: AnInt -> Int
    anIntToInt (AnInt i) = i

which fits perfectly well into the builtins machinery.

Although that becomes annoying for more complex data types. For tuples we need to provide two
projection functions ('fst' and 'snd') instead of a single pattern matcher, which is not too
bad, but to get pattern matching on lists we need three built-in functions: @null@, @head@ and
@tail@ and to require `Bool` to be in the universe to be able to define a PLC equivalent of

    matchList :: [a] -> r -> (a -> [a] -> r) -> r
    matchList xs z f = if null xs then z else f (head xs) (tail xs)

If a constructor stores more than one value, the corresponding projection function packs them
into a (possibly nested) pair, for example for

    data Data
        = Constr Integer [Data]
        | <...>

we have (pseudocode):

    unConstrData (Constr i ds) = (i, ds)

In order to get pattern matching over 'Data' we need a projection function per constructor as well
as with lists, but writing (where the @Data@ suffix indicates that a function is a builtin that
somehow corresponds to a constructor of 'Data')

    if isConstrData d
        then uncurry fConstr $ unConstrData d
        else if isMapData d
            then fMap $ unMapData d
            else if isListData d
                then fList $ unListData d
                else <...>

is tedious and inefficient and so instead we have a single @chooseData@ builtin that matches on
its @Data@ argument and chooses the appropriate branch (type instantiations and strictness concerns
are omitted for clarity):

     chooseData
        (uncurry fConstr $ unConstrData d)
        (fMap $ unMapData d)
        (fList $ unListData d)
        <...>
        d

which, for example, evaluates to @fMap es@ when @d@ is @Map es@

On the bright side, this encoding of pattern matchers does work, so maybe it's indeed worth to
prioritize performance over convenience, especially given the fact that performance is of a concern
to every single end user while the inconvenience is only a concern for the compiler writers and
we don't add complex built-in types too often.
-}

{- Note [Representable built-in functions over polymorphic built-in types]
In Note [Pattern matching on built-in types] we talked about how general higher-order polymorphic
built-in functions are troubling, but polymorphic built-in functions can be troubling even in
the first-order case. In a Plutus program we always pair constants of built-in types with their
tags from the universe, which means that in order to produce a constant embedded into a program
we need the tag of the type of that constant. We can't get that tag from a Plutus type -- those
are gone at runtime, so the only place we can get a type tag from during evaluation is some already
existing constant. I.e. the following built-in function is representable:

    tail : all a. [a] -> [a]

because for constructing the result we need a type tag for @[a]@, but we have a value of that type
as an argument and so we can extract the type tag from it. Same applies to

    swap : all a b. (a, b) -> (b, a)

since 'SomeConstantOf' always contains a type tag for each type that a polymorphic built-in type is
instantiated with and so constructing a type tag for @(b, a)@ given type tags for @a@ and @b@ is
unproblematic.

And so neither

    cons : all a. a -> [a] -> [a]

is troubling (even though that ones requires checking at runtime that the element to be prepended
is of the same type as the type of the elements of the list as it's impossible to enforce this kind
of type safety in Haskell over possibly untyped PLC).

However consider the following imaginary builtin:

    nil : all a. [a]

we can't represent it for two reasons:

1. we don't have any argument providing us a type tag for @a@ and hence we can't construct a type
   tag for @[a]@
2. it would be a very unsound builtin to have. We can only instantiate built-in types with other
   built-in types and so allowing @nil {some_non_built_in_type}@ would be a lie that couldn't reduce
   to anything since it's not even possible to represent a built-in list with non-built-in elements
   (even if there's zero of them)

"Wait, but wouldn't @cons {some_non_built_in_type}@ be a lie as well?" -- No! Since @cons@ does not
just construct a list filled with elements of a non-built-in type but also expects one as an
argument and providing such an argument is impossible, 'cause it's pretty much the same thing as
populating 'Void' -- both values are equally unrepresentable. And so @cons {some_non_built_in_type}@
is a way to say @absurd@, which is perfectly fine to have.

Finally,

    comma :: all a b. a -> b -> (a, b)

is representable (because we can require arguments to be constants carrying universes with them,
which we can use to construct the resulting universe), but is still a lie, because instantiating
that builtin with non-built-in types is possible and so the PLC type checker won't throw on such
an instantiation, which will become 'EvalutionFailure' at runtime the moment unlifting of a
non-constant is attempted when a constant is expected.

So could we still get @nil@ or a safe version of @comma@ somehow? Well, we could have this
weirdness:

    nilOfTypeOf : all a. [a] -> [a]

i.e. ask for an already existing list, but ignore the actual list and only use the type tag.

But since we're ignoring the actual list, can't we just not pass it in the first place? And instead
pass around our good old friends, singletons. We should be able to do that, but it hasn't been
investigated. Perhaps something along the lines of adding the following constructor to 'DefaultUni':

    DefaultUniProtoSing :: DefaultUni (Esc (Proxy @GHC.Type))

and then defining

    nil : all a. sing a -> [a]

and then the Plutus Tx compiler can provide a type class or something for constructing singletons
for built-in types.
-}
