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
    , AnEvaluator
    , Evaluator
    , unliftConstant
    , OpaqueTerm (..)
    , KnownType (..)
    , toTypeAst
    , readKnown
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

-- | A thing that evaluates @f@ in monad @m@, returns an @a@ and allows to extend the set of
-- dynamic built-in names.
type AnEvaluator f uni m a = DynamicBuiltinNameMeanings uni -> f TyName Name uni () -> m a

-- | A thing that evaluates @f@ in monad @m@ and allows to extend the set of
-- dynamic built-in names.
type Evaluator f uni m = AnEvaluator f uni m (Term TyName Name uni ())

{- Note [The reverse example]
Having a dynamic built-in with the following signature:

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

Note how we use 'OpaqueTerm' in order to wrap a PLC term as a Haskell value using 'readKnown' and
then unwrap the term back using 'makeKnown' without ever inspecting the term.
-}

-- See Note [The reverse example] for an example.
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

-- | Extract the 'Constant' from a 'Term'
-- (or throw an error if the term is not a 'Constant' or
-- the constant is not of the expected type).
unliftConstant
    :: forall a m uni err.
       ( MonadError (ErrorWithCause uni err) m, AsUnliftingError err
       , GShow uni, GEq uni, uni `Includes` a
       )
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

-- | Haskell types known to exist on the PLC side.
class KnownType uni a where
    -- | The type representing @a@ used on the PLC side.
    toTypeAstProxy :: Proxy a -> Type TyName uni ()

    -- | Convert a Haskell value to the corresponding PLC term.
    -- The inverse of 'readKnown'.
    makeKnown :: a -> Term TyName Name uni ()

    -- | Convert a PLC term to the corresponding Haskell value and supply it to the continuation.
    -- Needed to get 'DerivingVia' working ('readKnown' breaks it, because @a@ is inside a locally
    -- bound 'm'). Has no relation to bracket-like functions and therefore an @a@ must be allowed to
    -- escape the scope of the continuation.
    withReadKnown
        :: (MonadError (ErrorWithCause uni err) m, AsUnliftingError err)
        => Term TyName Name uni () -> (a -> m r) -> m r
    withReadKnown term k = readKnown term >>= k

toTypeAst :: forall uni a proxy. KnownType uni a => proxy a -> Type TyName uni ()
toTypeAst _ = toTypeAstProxy $ Proxy @a

-- | Convert a PLC term to the corresponding Haskell value.
-- The inverse of 'makeKnown'.
readKnown
    :: (KnownType uni a, MonadError (ErrorWithCause uni err) m, AsUnliftingError err)
    => Term TyName Name uni () -> m a
readKnown term = withReadKnown term return

newtype Meta a = Meta
    { unMeta :: a
    }

instance (GShow uni, GEq uni, uni `Includes` a) => KnownType uni (Meta a) where
    toTypeAstProxy _ = mkTyBuiltin @a ()
    makeKnown = mkConstant () . unMeta
    withReadKnown term k = unliftConstant term >>= k . Meta

instance KnownType uni a => KnownType uni (EvaluationResult a) where
    toTypeAstProxy _ = toTypeAst $ Proxy @a

    -- 'EvaluationFailure' on the Haskell side becomes 'Error' on the PLC side.
    makeKnown EvaluationFailure     = Error () $ toTypeAst (Proxy @a)
    makeKnown (EvaluationSuccess x) = makeKnown x

    -- Catching 'EvaluationFailure' here would allow *not* to short-circuit when 'readKnown' fails
    -- to read a Haskell value of type @a@. Instead, in the denotation of the builtin function
    -- the programmer would be given an explicit 'EvaluationResult' value to handle, which means
    -- that when this value is 'EvaluationFailure', a PLC 'Error' was caught.
    -- I.e. it would essentially allow to catch errors and handle them in a programmable way.
    -- We forbid this, because it complicates code and is not supported by evaluation engines anyway.
    withReadKnown _ _ = throwingWithCause _UnliftingError "Error catching is not supported" Nothing

instance (KnownSymbol text, KnownNat uniq, uni ~ uni') =>
            KnownType uni (OpaqueTerm uni' text uniq) where
    toTypeAstProxy _ =
        TyVar () . TyName $
            Name ()
                (Text.pack $ symbolVal @text Proxy)
                (Unique . fromIntegral $ natVal @uniq Proxy)

    makeKnown = unOpaqueTerm

    withReadKnown term k = k $ OpaqueTerm term

type KnownBuiltinType uni a = (GShow uni, GEq uni, uni `Includes` a)

deriving via Meta Integer instance KnownBuiltinType uni Integer => KnownType uni Integer
deriving via Meta BSL.ByteString instance KnownBuiltinType uni BSL.ByteString => KnownType uni BSL.ByteString
deriving via Meta String instance KnownBuiltinType uni String => KnownType uni String
deriving via Meta Char instance KnownBuiltinType uni Char => KnownType uni Char
deriving via Meta () instance KnownBuiltinType uni () => KnownType uni ()
deriving via Meta Bool instance KnownBuiltinType uni Bool => KnownType uni Bool
