-- | This module assigns types to built-ins.
-- See the @plutus/plutus-core/docs/Constant application.md@
-- article for how this emerged.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Constant.Typed
    ( KnownKind (..)
    , TypeScheme (..)
    , FoldArgs
    , FoldArgsEx
    , unliftConstant
    , TyVarRep
    , TyAppRep
    , Opaque (..)
    , AsConstant (..)
    , FromConstant (..)
    , HasConstant
    , HasConstantIn
    , KnownTypeAst (..)
    , KnownType (..)
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Evaluation.Machine.Exception
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Control.Monad.Except
import qualified Data.ByteString                                    as BS
import qualified Data.Kind                                          as GHC (Type)
import           Data.Proxy
import           Data.String
import qualified Data.Text                                          as Text
import           GHC.TypeLits

infixr 9 `TypeSchemeArrow`

-- | A class for converting Haskell kinds to PLC kinds.
class KnownKind kind where
    knownKind :: proxy kind -> Kind ()

instance KnownKind GHC.Type where
    knownKind _ = Type ()

instance (KnownKind dom, KnownKind cod) => KnownKind (dom -> cod) where
    knownKind _ = KindArrow () (knownKind $ Proxy @dom) (knownKind $ Proxy @cod)

-- | Type schemes of primitive operations.
-- @as@ is a list of types of arguments, @r@ is the resulting type.
-- E.g. @Char -> Bool -> Integer@ is encoded as @TypeScheme term [Char, Bool] Integer@.
data TypeScheme term (args :: [GHC.Type]) res where
    TypeSchemeResult
        :: KnownType term res
        => Proxy res -> TypeScheme term '[] res
    TypeSchemeArrow
        :: KnownType term arg
        => Proxy arg -> TypeScheme term args res -> TypeScheme term (arg ': args) res
    TypeSchemeAll
        :: (KnownSymbol text, KnownNat uniq, KnownKind kind)
           -- Here we require the user to manually provide the unique of a type variable.
           -- That's nothing but silly, but I do not see what else we can do with the current design.
        => Proxy '(text, uniq, kind)
           -- We use a funny trick here: instead of binding
           --
           -- > TypedBuiltin (Opaque term (TyVarRep text uniq))
           --
           -- directly we introduce an additional and "redundant" type variable. The reason why we
           -- do that is because this way we can also bind such a variable later when constructing
           -- the 'TypeScheme' of a polymorphic builtin, so that for the user this looks exactly
           -- like a single bound type variable instead of this weird @Opaque@ thing.
           --
           -- And note that in most cases we do not need to bind anything at the type level and can
           -- use the variable bound at the term level directly, because it's of the type that
           -- 'TypeSchemeResult' expects. Type-level binding is only needed when you want to apply
           -- a type constructor to the variable, like in
           --
           -- > reverse : all a. list a -> list a
        -> (forall (ot :: kind). ot ~ TyVarRep text uniq => Proxy ot -> TypeScheme term args res)
        -> TypeScheme term args res

-- | Turn a list of Haskell types @as@ into a functional type ending in @r@.
--
-- >>> :set -XDataKinds
-- >>> :kind! FoldArgs [Char, Bool] Integer
-- FoldArgs [Char, Bool] Integer :: *
-- = Char -> Bool -> Integer
type family FoldArgs args res where
    FoldArgs '[]           res = res
    FoldArgs (arg ': args) res = arg -> FoldArgs args res

-- | Calculates the parameters of the costing function for a builtin.
type family FoldArgsEx args where
    FoldArgsEx '[]           = ExBudget
    FoldArgsEx (arg ': args) = ExMemory -> FoldArgsEx args

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

E.g. Having a built-in function with the following signature (assuming we somehow have a PLC @list@
mapping to Haskell @[]@ -- that was possible before, but not now, but the example is still instructive):

    reverse : all a. list a -> list a

that maps to Haskell's

    reverse :: forall a. [a] -> [a]

evaluation of

    PLC.reverse {bool} (cons true (cons false nil))

proceeds as follows:

      PLC.reverse {bool} (cons true (cons false nil))
    ~ makeKnown (Haskell.reverse (readKnown (cons true (cons false nil))))
    ~ makeKnown (Haskell.reverse [Opaque true, Opaque false])
    ~ makeKnown [Opaque false, Opaque true]
    ~ EvaluationSuccess (cons false (cons true nil))

Note how we use the 'Opaque' wrapper in order to unlift a PLC term as an opaque Haskell value
using 'readKnown' and then lift the term back using 'makeKnown' without ever inspecting the term.

@Opaque term rep@ can be used for passing any @term@ through the builtin application machinery,
not just one whose type is a bound variable. For example, you can define a new data type

    data NatRep

provide a 'KnownTypeAst' instance for it (mapping a @Proxy NatRep@ to the actual type of natural
numbers in PLC) and define a (rather pointless) builtin like @idNat : nat -> nat@.

It's also possible to bind a type variable of a higher-kind, say, @f :: * -> *@ and make a builtin
with the following signature:

    idFInteger : all (f :: * -> *). f integer -> f integer

where the type application is handled with 'TyAppRep'

It would be much better if we didn't need to define that @*Rep@ stuff at the type level just to
demote it to the term level via a type class, but this hasn't been investigated yet. A plausible
way would be to ditch 'KnownTypeAst' (but keep 'KnownType') and provide PLC types manually.
But that doesn't seem to give rise to a terribly nice API.

The implementation is rather straightforward, but there is one catch, namely that it takes some care
to adapt the CEK machine to handle polymorphic built-in functions,
see https://github.com/input-output-hk/plutus/issues/1882
-}

-- | Representation of a type variable: its name and unique.
data family TyVarRep (text :: Symbol) (unique :: Nat) :: kind

-- | Representation of a type application: a function and an argument.
data family TyAppRep (fun :: dom -> cod) (arg :: dom) :: cod

-- See Note [Motivation for polymorphic built-in functions]
-- See Note [Implemetation of polymorphic built-in functions]
-- | The denotation of a term whose PLC type is encoded in @rep@ (for example a type variable or
-- an application of a type variable). I.e. the denotation of such a term is the term itself.
-- This is because we have parametricity in Haskell, so we can't inspect a value whose
-- type is, say, a bound variable, so we never need to convert such a term from Plutus Core to
-- Haskell and back and instead can keep it intact.
newtype Opaque term (rep :: GHC.Type) = Opaque
    { unOpaque :: term
    } deriving newtype (Pretty)

class AsConstant term where
    -- | Unwrap a shallowly embedded Haskell value from a @term@ or fail.
    asConstant :: term -> Maybe (Some (ValueOf (UniOf term)))

class FromConstant term where
    -- | Wrap a Haskell value as a @term@.
    fromConstant :: Some (ValueOf (UniOf term)) -> term

instance AsConstant (Term TyName Name uni fun ann) where
    asConstant (Constant _ val) = Just val
    asConstant _                = Nothing

instance (Closed uni, uni `Everywhere` ExMemoryUsage) =>
            FromConstant (Term tyname name uni fun ExMemory) where
    fromConstant value = Constant (memoryUsage value) value

instance FromConstant (Term tyname name uni fun ()) where
    fromConstant = Constant ()

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from.
--
-- 'AsConstant' and 'FromConstant' are separate, because we need only one instance of 'AsConstant'
-- per 'Term'-like type and 'FromConstant' requires as many instances as there are different kinds
-- of annotations (we're mostly interested in 'ExMemory' and @()@). Originally we had a single type
-- class but it proved to be less efficient than having two of them.
type HasConstant term = (AsConstant term, FromConstant term)

-- | Ensures that @term@ has a 'Constant'-like constructor to lift values to and unlift values from
-- and connects @term@ and its @uni@.
type HasConstantIn uni term = (UniOf term ~ uni, HasConstant term)

-- | Extract the 'Constant' from a 'Term'
-- (or throw an error if the term is not a 'Constant' or the constant is not of the expected type).
unliftConstant
    :: forall a m term err.
       (MonadError (ErrorWithCause err term) m, AsUnliftingError err, KnownBuiltinType term a)
    => term -> m a
unliftConstant term = case asConstant term of
    Just (Some (ValueOf uniAct x)) -> do
        let uniExp = knownUni @(UniOf term) @a
        case uniAct `geq` uniExp of
            Just Refl -> pure x
            Nothing   -> do
                let err = fromString $ concat
                        [ "Type mismatch: "
                        , "expected: " ++ gshow uniExp
                        , "; actual: " ++ gshow uniAct
                        ]
                throwingWithCause _UnliftingError err $ Just term
    Nothing -> throwingWithCause _UnliftingError "Not a constant" $ Just term

{- Note [KnownType's defaults]
We'd like to use @default@ for providing instances for built-in types instead of @DerivingVia@,
because the latter breaks on @m a@

It's possible to circumvent this, by using @forall r. (a -> m r) -> m r@ instead,
but then we need to recover the original handy definitions and make the API and
the code bloated (instances are more verbose with @DerivingVia@).

We don't use @default@ in 'KnownTypeAst', because an attempt to write

    default toTypeAst :: (k ~ GHC.Type, uni `Includes` a) => proxy a -> Type TyName uni ()
    toTypeAst = toBuiltinTypeAst

results in

    Expected kind '* -> *', but 'uni' has kind 'k -> *'
-}

class KnownTypeAst uni (a :: k) where
    -- | The type representing @a@ used on the PLC side.
    toTypeAst :: proxy a -> Type TyName uni ()

-- | A constraint for \"@a@ is a 'KnownType' by means of being included in @uni@\".
type KnownBuiltinType term a =
    (HasConstant term, GShow (UniOf term), GEq (UniOf term), UniOf term `Includes` a)

-- See Note [KnownType's defaults].
-- | A default implementation of 'toTypeAst' for built-in types.
toBuiltinTypeAst :: uni `Includes` a => proxy a -> Type TyName uni ()
toBuiltinTypeAst (_ :: proxy a) = mkTyBuiltin @a ()

-- See Note [KnownType's defaults]
-- | Haskell types known to exist on the PLC side.
class KnownTypeAst (UniOf term) a => KnownType term a where
    -- | Convert a Haskell value to the corresponding PLC term.
    -- The inverse of 'readKnown'.
    makeKnown :: a -> EvaluationResult term
    default makeKnown :: KnownBuiltinType term a => a -> EvaluationResult term
    -- We need @($!)@, because otherwise Haskell expressions are thrown away rather than being
    -- evaluated and we use 'unsafePerformIO' for logging, so we want to compute the Haskell value
    -- just for side effects that the evaluation may cause.
    makeKnown x = EvaluationSuccess . fromConstant . someValue $! x

    -- | Convert a PLC term to the corresponding Haskell value.
    -- The inverse of 'makeKnown'.
    readKnown
        :: (MonadError (ErrorWithCause err term) m, AsUnliftingError err)
        => term -> m a
    default readKnown
        :: (MonadError (ErrorWithCause err term) m, AsUnliftingError err, KnownBuiltinType term a)
        => term -> m a
    readKnown = unliftConstant

instance KnownTypeAst uni a => KnownTypeAst uni (EvaluationResult a) where
    toTypeAst _ = toTypeAst $ Proxy @a

instance (KnownTypeAst (UniOf term) a, KnownType term a) =>
            KnownType term (EvaluationResult a) where
    makeKnown mx = mx >>= makeKnown

    -- Catching 'EvaluationFailure' here would allow *not* to short-circuit when 'readKnown' fails
    -- to read a Haskell value of type @a@. Instead, in the denotation of the builtin function
    -- the programmer would be given an explicit 'EvaluationResult' value to handle, which means
    -- that when this value is 'EvaluationFailure', a PLC 'Error' was caught.
    -- I.e. it would essentially allow to catch errors and handle them in a programmable way.
    -- We forbid this, because it complicates code and is not supported by evaluation engines anyway.
    readKnown = throwingWithCause _UnliftingError "Error catching is not supported" . Just

instance (KnownSymbol text, KnownNat uniq) => KnownTypeAst uni (TyVarRep text uniq) where
    toTypeAst _ =
        TyVar () . TyName $
            Name (Text.pack $ symbolVal @text Proxy)
                 (Unique . fromIntegral $ natVal @uniq Proxy)

instance (KnownTypeAst uni fun, KnownTypeAst uni arg) => KnownTypeAst uni (TyAppRep fun arg) where
    toTypeAst _ = TyApp () (toTypeAst $ Proxy @fun) (toTypeAst $ Proxy @arg)

instance KnownTypeAst uni rep => KnownTypeAst uni (Opaque term rep) where
    toTypeAst _ = toTypeAst $ Proxy @rep

instance (term ~ term', KnownTypeAst (UniOf term) rep) => KnownType term (Opaque term' rep) where
    makeKnown = EvaluationSuccess . unOpaque
    readKnown = pure . Opaque

instance uni `Includes` Integer       => KnownTypeAst uni Integer       where
    toTypeAst = toBuiltinTypeAst
instance uni `Includes` BS.ByteString => KnownTypeAst uni BS.ByteString where
    toTypeAst = toBuiltinTypeAst
instance uni `Includes` String        => KnownTypeAst uni String        where
    toTypeAst = toBuiltinTypeAst
instance uni `Includes` Char          => KnownTypeAst uni Char          where
    toTypeAst = toBuiltinTypeAst
instance uni `Includes` ()            => KnownTypeAst uni ()            where
    toTypeAst = toBuiltinTypeAst
instance uni `Includes` Bool          => KnownTypeAst uni Bool          where
    toTypeAst = toBuiltinTypeAst

instance KnownBuiltinType term Integer       => KnownType term Integer
instance KnownBuiltinType term BS.ByteString => KnownType term BS.ByteString
instance KnownBuiltinType term String        => KnownType term String
instance KnownBuiltinType term Char          => KnownType term Char
instance KnownBuiltinType term ()            => KnownType term ()
instance KnownBuiltinType term Bool          => KnownType term Bool
