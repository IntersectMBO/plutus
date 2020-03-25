-- | This module assigns types to built-ins.
-- See the @plutus/language-plutus-core/docs/Constant application.md@
-- article for how this emerged.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.Typed
    ( TypeScheme (..)
    , TypedBuiltinName (..)
    , FoldArgs
    , DynamicBuiltinNameMeaning (..)
    , DynamicBuiltinNameDefinition (..)
    , DynamicBuiltinNameMeanings (..)
    , unliftConstant
    , OpaqueTerm (..)
    , KnownType (..)
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Control.Monad.Except
import qualified Data.ByteString.Lazy                               as BSL
import qualified Data.Kind                                          as GHC (Type)
import           Data.Map                                           (Map)
import           Data.Proxy
import           Data.String
import qualified Data.Text                                          as Text
import           GHC.TypeLits

infixr 9 `TypeSchemeArrow`

-- | Type schemes of primitive operations.
-- @as@ is a list of types of arguments, @r@ is the resulting type.
-- E.g. @Char -> Bool -> Integer@ is encoded as @TypeScheme uni [Char, Bool] Integer@.
data TypeScheme uni (args :: [GHC.Type]) res where
    TypeSchemeResult
        :: KnownType uni res => Proxy res -> TypeScheme uni '[] res
    TypeSchemeArrow
        :: KnownType uni arg
        => Proxy arg -> TypeScheme uni args res -> TypeScheme uni (arg ': args) res
    TypeSchemeAllType
        :: (KnownSymbol text, KnownNat uniq)
           -- Here we require the user to manually provide the unique of a type variable.
           -- That's nothing but silly, but I do not see what else we can do with the current design.
           -- Once the 'BuiltinPipe' thing gets implemented, we'll be able to bind 'uniq' inside
           -- the continuation and also put there the @KnownNat uniq@ constraint
           -- (i.e. use universal quantification for uniques) and that should work alright.
        => Proxy '(text, uniq)
           -- We use a funny trick here: instead of binding
           --
           -- > TypedBuiltin (OpaqueTerm uni text uniq)
           --
           -- directly we introduce an additional and "redundant" type variable. The reason why we
           -- do that is because this way we can also bind such a variable later when constructing
           -- the 'TypeScheme' of a polymorphic builtin, so that for the user this looks exactly
           -- like a single bound type variable instead of this weird @OpaqueTerm text uniq@ thing.
           --
           -- And note that in most cases we do not need to bind anything at the type level and can
           -- use the variable bound at the term level directly, because it's of the type that
           -- 'TypeSchemeResult' expects. Type-level binding is only needed when you want to apply
           -- a type constructor to the variable, like in
           --
           -- > reverse : all a. list a -> list a
        -> (forall ot. ot ~ OpaqueTerm uni text uniq => Proxy ot -> TypeScheme uni args res)
        -> TypeScheme uni args res

-- | A 'BuiltinName' with an associated 'TypeScheme'.
data TypedBuiltinName uni args res = TypedBuiltinName BuiltinName (TypeScheme uni args res)

-- | Turn a list of Haskell types @as@ into a functional type ending in @r@.
--
-- >>> :set -XDataKinds
-- >>> :kind! FoldArgs [Char, Bool] Integer
-- FoldArgs [Char, Bool] Integer :: *
-- = Char -> Bool -> Integer
type family FoldArgs args r where
    FoldArgs '[]           res = res
    FoldArgs (arg ': args) res = arg -> FoldArgs args res

{- Note [DynamicBuiltinNameMeaning]
We represent the meaning of a 'DynamicBuiltinName' as a 'TypeScheme' and a Haskell denotation.
We need both while evaluting a 'DynamicBuiltinName', because 'TypeScheme' is required for
well-typedness to avoid using 'unsafeCoerce' and similar junk, while the denotation is what
actually computes. We do not need denotations for type checking, nor strongly typed 'TypeScheme'
is required, however analogously to static built-ins, we compute the types of dynamic built-ins from
their 'TypeScheme's. This way we only define a 'TypeScheme', which we anyway need, and then compute
the corresponding 'Type' from it. And we can't go the other way around -- from untyped to typed --
of course. Therefore a typed thing has to go before the corresponding untyped thing and in the
final pipeline one has to supply a 'DynamicBuiltinNameMeaning' for each of the 'DynamicBuiltinName's.
-}

-- See Note [DynamicBuiltinNameMeaning].
-- | The meaning of a dynamic built-in name consists of its 'Type' represented as a 'TypeScheme'
-- and its Haskell denotation.
data DynamicBuiltinNameMeaning uni =
    forall args res. DynamicBuiltinNameMeaning
        (TypeScheme uni args res)
        (FoldArgs args res)
        (FoldArgs args ExBudget)

-- | The definition of a dynamic built-in consists of its name and meaning.
data DynamicBuiltinNameDefinition uni =
    DynamicBuiltinNameDefinition DynamicBuiltinName (DynamicBuiltinNameMeaning uni)

-- | Mapping from 'DynamicBuiltinName's to their 'DynamicBuiltinNameMeaning's.
newtype DynamicBuiltinNameMeanings uni = DynamicBuiltinNameMeanings
    { unDynamicBuiltinNameMeanings :: Map DynamicBuiltinName (DynamicBuiltinNameMeaning uni)
    } deriving (Semigroup, Monoid)

{- Note [Motivation for polymorphic built-in functions]
We need to support polymorphism for built-in functions for these reasons:

1. @ifThenElse@ for 'Bool' (being a built-in type rather than a Scott-encoded one) has to be
   polymorphic as its type signature is

       ifThenElse : all a. Bool -> a -> a -> a

   Previously we had 'Bool' as a Scott-encoded type, but this required plenty of supporting machinery,
   because unlifting (aka Scott-decoding) a PLC 'Bool' into a Haskell 'Bool' is quite a non-trivial
   thing, see https://github.com/input-output-hk/plutus/blob/e222466e6d46bbca9f76243bb496b3c88ed02ca1/language-plutus-core/src/Language/PlutusCore/Constant/Typed.hs#L165-L252

   Now that we got rid of all this complexity we have to pay for that by supporting polymorphic
   built-in functions (but we added that support long ago anyway, 'cause it was easy to do).

2. we may want to add efficient polymorphic built-in types like @IntMap@ or @Vector@ and most functions
   defined over them are polymorphic as well
-}

{- Note [Implemetation of polymorphic built-in functions]
Encoding polymorphism in an AST in an intrinsically typed manner is not a pleasant thing to do in Haskell.
It's not impossible, see "Embedding F", Sam Lindley: http://homepages.inf.ed.ac.uk/slindley/papers/embedding-f.pdf
But we'd rather avoid such heavy techniques.

Fortunately, there is a simple trick: we have parametricity in Haskell, so a function that is
polymorphic in its argument can't inspect that argument in any way and so we never actually need to
convert such an argument from PLC to Haskell just to convert it back later without ever inspecting
the value. Instead we can keep the argument intact and apply the Haskell function directly to
the PLC AST representing some value.

E.g. Having a built-in function with the following signature:

    reverse : all a. list a -> list a

that maps to Haskell's

    reverse :: forall a. [a] -> [a]

evaluation of

    PLC.reverse {bool} (cons true (cons false nil))

proceeds as follows:

      PLC.reverse {bool} (cons true (cons false nil))
    ~ makeKnown (Haskell.reverse (readKnown (cons true (cons false nil))))
    ~ makeKnown (Haskell.reverse [OpaqueTerm true, OpaqueTerm false])
    ~ makeKnown [OpaqueTerm false, OpaqueTerm true]
    ~ cons false (cons true nil)

Note how we use the 'OpaqueTerm' wrapper in order to unlift a PLC term as an opaque Haskell value
using 'readKnown' and then lift the term back using 'makeKnown' without ever inspecting the term.

The implementation is rather straightforward, but there is one catch, namely that it takes some care
to adapt the CEK machine to handle polymorphic built-in functions,
see https://github.com/input-output-hk/plutus/issues/1882
-}

-- See Note [Motivation for polymorphic built-in functions]
-- See Note [Implemetation of polymorphic built-in functions]
-- | The denotation of a term whose type is a bound variable.
-- I.e. the denotation of such a term is the term itself.
-- This is because we have parametricity in Haskell, so we can't inspect a value whose
-- type is a bound variable, so we never need to convert such a term from Plutus Core to Haskell
-- and back and instead can keep it intact.
newtype OpaqueTerm uni (text :: Symbol) (unique :: Nat) = OpaqueTerm
    { unOpaqueTerm :: Term TyName Name uni ()
    }

instance (GShow uni, Closed uni, uni `Everywhere` Pretty) =>
            Pretty (OpaqueTerm uni text unique) where
    pretty = pretty . unOpaqueTerm

-- | A constraint for \"@a@ is a 'KnownType' by means of being included in @uni@\".
class (GShow uni, GEq uni, uni `Includes` a) => KnownBuiltinType uni a
instance (GShow uni, GEq uni, uni `Includes` a) => KnownBuiltinType uni a

-- | Extract the 'Constant' from a 'Term'
-- (or throw an error if the term is not a 'Constant' or the constant is not of the expected type).
unliftConstant
    :: forall a m uni err.
       (MonadError (ErrorWithCause uni err) m, AsUnliftingError err, KnownBuiltinType uni a)
    => Term TyName Name uni () -> m a
unliftConstant term = case term of
    Constant () (Some (ValueOf uniAct x)) -> do
        let uniExp = knownUni @uni @a
        case uniAct `geq` uniExp of
            Just Refl -> pure x
            Nothing   -> do
                let err = fromString $ concat
                        [ "Type mismatch: "
                        , "expected: " ++ gshow uniExp
                        , "actual: " ++ gshow uniAct
                        ]
                throwingWithCause _UnliftingError err $ Just term
    _ -> throwingWithCause _UnliftingError "Not a constant" $ Just term

{- Note [KnownType's defaults]
We use @default@ for providing instances for built-in types instead of @DerivingVia@,
because the latter breaks on

    1. proxy a
    2. m a

It's possible to circumvent this, by using

    1. Proxy a
    2. forall r. (a -> m r) -> m r

instead, but then we need to recover the original handy definitions and
make the API and the code bloated (instances are more verbose with @DerivingVia@).
-}

-- See Note [KnownType's defaults]
-- | Haskell types known to exist on the PLC side.
class KnownType uni a where
    -- | The type representing @a@ used on the PLC side.
    toTypeAst :: proxy a -> Type TyName uni ()
    default toTypeAst :: KnownBuiltinType uni a => proxy a -> Type TyName uni ()
    toTypeAst _ = mkTyBuiltin @a ()

    -- | Convert a Haskell value to the corresponding PLC term.
    -- The inverse of 'readKnown'.
    makeKnown :: a -> Term TyName Name uni ()
    default makeKnown :: KnownBuiltinType uni a => a -> Term TyName Name uni ()
    -- We need @($!)@, because otherwise Haskell expressions are thrown away rather than being
    -- evaluated and we use 'unsafePerformIO' for logging, so we want to compute the Haskell value
    -- just for side effects that the evaluation may cause.
    makeKnown x = mkConstant () $! x

    -- | Convert a PLC term to the corresponding Haskell value.
    -- The inverse of 'makeKnown'.
    readKnown
        :: (MonadError (ErrorWithCause uni err) m, AsUnliftingError err)
        => Term TyName Name uni () -> m a
    default readKnown
        :: (MonadError (ErrorWithCause uni err) m, AsUnliftingError err, KnownBuiltinType uni a)
        => Term TyName Name uni () -> m a
    readKnown = unliftConstant

instance KnownType uni a => KnownType uni (EvaluationResult a) where
    toTypeAst _ = toTypeAst $ Proxy @a

    -- 'EvaluationFailure' on the Haskell side becomes 'Error' on the PLC side.
    makeKnown EvaluationFailure     = Error () $ toTypeAst (Proxy @a)
    makeKnown (EvaluationSuccess x) = makeKnown x

    -- Catching 'EvaluationFailure' here would allow *not* to short-circuit when 'readKnown' fails
    -- to read a Haskell value of type @a@. Instead, in the denotation of the builtin function
    -- the programmer would be given an explicit 'EvaluationResult' value to handle, which means
    -- that when this value is 'EvaluationFailure', a PLC 'Error' was caught.
    -- I.e. it would essentially allow to catch errors and handle them in a programmable way.
    -- We forbid this, because it complicates code and is not supported by evaluation engines anyway.
    readKnown _ = throwingWithCause _UnliftingError "Error catching is not supported" Nothing

instance (KnownSymbol text, KnownNat uniq, uni ~ uni') =>
            KnownType uni (OpaqueTerm uni' text uniq) where
    toTypeAst _ =
        TyVar () . TyName $
            Name ()
                (Text.pack $ symbolVal @text Proxy)
                (Unique . fromIntegral $ natVal @uniq Proxy)

    makeKnown = unOpaqueTerm

    readKnown = pure . OpaqueTerm

instance KnownBuiltinType uni Integer        => KnownType uni Integer
instance KnownBuiltinType uni BSL.ByteString => KnownType uni BSL.ByteString
instance KnownBuiltinType uni String         => KnownType uni String
instance KnownBuiltinType uni Char           => KnownType uni Char
instance KnownBuiltinType uni ()             => KnownType uni ()
instance KnownBuiltinType uni Bool           => KnownType uni Bool
