{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
-- | This module assigns types to built-ins.Typed
-- See the @plutus/language-plutus-core/docs/Constant application.md@
-- article for how this emerged.

{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE DerivingVia               #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TypeApplications          #-}

module Language.PlutusCore.Constant.Typed where
--     ( TypeGround (..)
--     , TypeScheme (..)
--     , FoldType
--     , TypedBuiltinName (..)
--     , NameMeaning (..)
--     , NameDefinition (..)
--     , NameMeanings (..)
--     , OpaqueTerm (..)
-- --     , InExtended (..)
-- --     , InUnextended (..)
--     , substConstantsType
--     , substConstantsTerm
--     , shiftConstantsType
--     , shiftConstantsTerm
--     , unshiftConstantsTerm
--     , shiftNameMeaning
-- --     , unshiftNameMeaning
-- --     , extractValueOf
-- --     , extractValue
-- --     , extractExtension
-- --     , embedNameMeanings
--     ) where

import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Lexer.Type hiding (name)
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Type
import           Language.PlutusCore.Constant.Universe

import           Data.GADT.Compare
import           Data.Map                                    (Map)
import           Data.Proxy
import           GHC.TypeLits

infixr 9 `TypeSchemeArrow`

data TypeGround uni a where
    TypeGroundValue  :: uni a -> TypeGround uni a
    TypeGroundResult :: uni a -> TypeGround uni (EvaluationResult a)
    TypeGroundTerm
        :: (forall a. uni' a -> uni a)
        -> (forall a. uni a -> uni' a)
        -> TypeGround uni (OpaqueTerm uni' text uniq)

-- | Type schemes of primitive operations.
-- @a@ is the Haskell denotation of a PLC type represented as a 'TypeScheme'.
-- @r@ is the resulting type in @a@, e.g. the resulting type in
-- @ByteString -> Size -> Integer@ is @Integer@.
data TypeScheme uni as r where
    TypeSchemeResult  :: TypeGround uni a -> TypeScheme uni '[] a
    TypeSchemeArrow   :: TypeGround uni a -> TypeScheme uni as r -> TypeScheme uni (a ': as) r
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
           -- > TypedBuiltin (OpaqueTerm text uniq)
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
        -> (forall ot. ot ~ OpaqueTerm uni text uniq => TypeGround uni ot -> TypeScheme uni as r)
        -> TypeScheme uni as r

    -- The @r@ is rather ad hoc and needed only for tests.
    -- We could use type families to compute it instead of storing as an index.
    -- That's a TODO perhaps.

-- | A 'BuiltinName' with an associated 'TypeScheme'.
data TypedBuiltinName uni as r = TypedBuiltinName BuiltinName (TypeScheme uni as r)

{- Note [NameMeaning]
We represent the meaning of a 'DynamicBuiltinName' as a 'TypeScheme' and a Haskell denotation.
We need both while evaluting a 'DynamicBuiltinName', because 'TypeScheme' is required for
well-typedness to avoid using 'unsafeCoerce' and similar junk, while the denotation is what
actually computes. We do not need denotations for type checking, nor strongly typed 'TypeScheme'
is required, however analogously to static built-ins, we compute the types of dynamic built-ins from
their 'TypeScheme's. This way we only define a 'TypeScheme', which we anyway need, and then compute
the corresponding 'Type' from it. And we can't go the other way around -- from untyped to typed --
of course. Therefore a typed thing has to go before the corresponding untyped thing and in the
final pipeline one has to supply a 'NameMeaning' for each of the 'DynamicBuiltinName's.
-}

type family FoldType as r where
    FoldType '[]       r = r
    FoldType (a ': as) r = a -> FoldType as r

-- See Note [NameMeaning].
-- | The meaning of a dynamic built-in name consists of its 'Type' represented as a 'TypeScheme'
-- and its Haskell denotation.
data NameMeaning uni = forall as r. NameMeaning (TypeScheme uni as r) (FoldType as r)

-- | The definition of a dynamic built-in consists of its name and meaning.
data NameDefinition uni = NameDefinition DynamicBuiltinName (NameMeaning uni)

-- | Mapping from 'DynamicBuiltinName's to their 'NameMeaning's.
newtype NameMeanings uni = NameMeanings
    { unNameMeanings :: Map DynamicBuiltinName (NameMeaning uni)
    } deriving (Semigroup, Monoid)

-- -- See Note [The reverse example] for an example.
-- -- | The denotation of a term whose type is a bound variable.
-- -- I.e. the denotation of such a term is the term itself.
-- -- This is because we have parametricity in Haskell, so we can't inspect a value whose
-- -- type is a bound variable, so we never need to convert such a term from Plutus Core to Haskell
-- -- and back and instead can keep it intact.
-- data OpaqueTerm uni (text :: Symbol) (unique :: Nat) =
--     forall uni'. OpaqueTerm (forall a. uni' a -> uni a) (Term TyName Name uni' ())

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
    pretty = undefined
--     pretty = pretty . unOpaqueTerm

substConstantsType
    :: (forall a. uni1 a -> uni2 a) -> Type tyname uni1 ann -> Type tyname uni2 ann
substConstantsType h = go where
    go (TyConstant ann con)        = TyConstant ann $ mapSome h con
    go (TyLam ann name kind ty)    = TyLam ann name kind (go ty)
    go (TyForall ann name kind ty) = TyForall ann name kind (go ty)
    go (TyIFix ann pat arg)        = TyIFix ann (go pat) (go arg)
    go (TyApp ann fun arg)         = TyApp ann (go fun) (go arg)
    go (TyFun ann dom cod)         = TyFun ann (go dom) (go cod)
    go (TyVar ann name)            = TyVar ann name

-- Any clever implementation using 'Plated' or something?
substConstantsTerm
    :: (forall a. uni1 a -> uni2 a) -> Term tyname name uni1 ann -> Term tyname name uni2 ann
substConstantsTerm h = goTerm where
    goType = substConstantsType h

    goTerm (LamAbs ann name ty body)  = LamAbs ann name (goType ty) (goTerm body)
    goTerm (TyAbs ann name kind body) = TyAbs ann name kind (goTerm body)
    goTerm (IWrap ann pat arg term)   = IWrap ann (goType pat) (goType arg) (goTerm term)
    goTerm (Apply ann fun arg)        = Apply ann (goTerm fun) (goTerm arg)
    goTerm (Unwrap ann term)          = Unwrap ann (goTerm term)
    goTerm (Error ann ty)             = Error ann (goType ty)
    goTerm (TyInst ann term ty)       = TyInst ann (goTerm term) (goType ty)
    goTerm (Var ann name)             = Var ann name
    goTerm (Constant ann con)         = Constant ann $ mapSomeOf h con
    goTerm (Builtin ann bi)           = Builtin ann bi

shiftConstantsType :: Type tyname uni ann -> Type tyname (Extend b uni) ann
shiftConstantsType = substConstantsType Original

shiftConstantsTerm :: Term tyname name uni ann -> Term tyname name (Extend b uni) ann
shiftConstantsTerm = substConstantsTerm Original

unextend :: Extend b uni a -> uni a
unextend (Original uni) = uni
unextend Extension      = error "Can't unshift an 'Extension'"

unshiftConstantsType :: Type tyname (Extend b uni) ann -> Type tyname uni ann
unshiftConstantsType = substConstantsType unextend

unshiftConstantsTerm :: Term tyname name (Extend b uni) ann -> Term tyname name uni ann
unshiftConstantsTerm = substConstantsTerm unextend

extractValueOf :: GEq uni => uni a -> Term tyname name uni ann -> Maybe a
extractValueOf uni1 (Constant _ (SomeOf uni2 x)) = fmap (\Refl -> x) $ geq uni1 uni2
extractValueOf _    _                            = Nothing

extractValue :: (GEq uni, uni `Includes` a)  => Term tyname name uni ann -> Maybe a
extractValue = extractValueOf knownUni

-- | Like @extractValueOf Extension@, but doesn't require any constraints.
extractExtension :: Term tyname name (Extend b uni) ann -> Maybe b
extractExtension (Constant _ (SomeOf Extension x)) = Just x
extractExtension _                                 = Nothing

shiftTypeGround :: TypeGround uni a -> TypeGround (Extend b uni) a
shiftTypeGround (TypeGroundValue  uni)  = TypeGroundValue  $ Original uni
shiftTypeGround (TypeGroundResult uni)  = TypeGroundResult $ Original uni
shiftTypeGround (TypeGroundTerm inj ej) = TypeGroundTerm (Original . inj) (ej . unextend)

unshiftTypeGround :: TypeGround (Extend b uni) a -> TypeGround uni a
unshiftTypeGround (TypeGroundValue  uni)  = TypeGroundValue  $ unextend uni
unshiftTypeGround (TypeGroundResult uni)  = TypeGroundResult $ unextend uni
unshiftTypeGround (TypeGroundTerm ej inj) = TypeGroundTerm (unextend . ej) (inj . Original)

shiftNameMeaning :: NameMeaning uni -> NameMeaning (Extend b uni)
shiftNameMeaning (NameMeaning sch x) =
    go sch $ \sch' inj -> NameMeaning sch' $ inj x where
        go
            :: TypeScheme uni as r
            -> (forall as' r'.
                    TypeScheme (Extend b uni) as' r' -> (FoldType as r -> FoldType as' r') -> c)
            -> c
        go (TypeSchemeResult gt)        k =
            k (TypeSchemeResult $ shiftTypeGround gt) id
        go (TypeSchemeArrow gt schB)    k =
            go schB $ \schB' inj -> k
                (TypeSchemeArrow (shiftTypeGround gt) schB')
                (\f -> inj . f)
        go (TypeSchemeAllType var schK) k =
            go (schK $ TypeGroundTerm id id) $ \schB' inj ->
                k (TypeSchemeAllType var $ \_ -> schB') inj

unshiftNameMeaning :: NameMeaning (Extend b uni) -> NameMeaning uni
unshiftNameMeaning (NameMeaning sch x) =
    go sch $ \sch' inj -> NameMeaning sch' $ inj x where
        go
            :: TypeScheme (Extend b uni) as r
            -> (forall as' r'.
                    TypeScheme uni as' r' -> (FoldType as r -> FoldType as' r') -> c)
            -> c
        go (TypeSchemeResult gt)        k =
            k (TypeSchemeResult $ unshiftTypeGround gt) id
        go (TypeSchemeArrow gt schB)    k =
            go schB $ \schB' inj -> k
                (TypeSchemeArrow (unshiftTypeGround gt) schB')
                (\f -> inj . f)
        go (TypeSchemeAllType var schK) k =
            go (schK $ TypeGroundTerm id id) $ \schB' inj ->
                k (TypeSchemeAllType var $ \_ -> schB') inj

embedNameMeanings
    :: (NameMeaning uni -> NameMeaning uni') -> NameMeanings uni -> NameMeanings uni'
embedNameMeanings emb (NameMeanings means) = NameMeanings $ fmap emb means

{-
One possible option is to continue using the current way to unlift things, but do not use it in the contant application machinery, where those implicit conversions between PLC and Haskell only complicate things and do not seem to be useful at all. Separating unlifting and evaluation makes perfect sense, but that also means that we'll have to define two distinct `TypeScheme` types: one for unlifting (with `KnownType` under the hood) and one for constant application machinery (with the recently described `TypeGround` under the hood), but what about dynamic builtin names then? We need to use them with both the `TypeScheme`s, because we need them generally (which covers the `TypeGround` case) and because we need to add new dynamic builtin types during unlifting (which covers the `KnownType` case).

It is possible to unify the two `TypeScheme`s and make conversions between PLC and Haskell explicit, but then we're back into the realms of passing evaluators around, having monadic constant application machinery, etc. And back to the securiry problem of allowing users to amend how evaluation proceeds by providing `KnownType` instances.

Maybe two distinct `TypeScheme` types is not much of a problem. The one used for unlifting will only be available internally and not exposed to anybody. The other one will be relevant to the blockchain owner deciding what types to make available for the end user. And the end user will just use whatever they're given access to, as they would expect.

... but with two kinds of dynamic builtin names, we also have to keep two kinds of environments? And we have to handle both the kinds of dynamic builtin names in the constant application machinery? I.e.

Need to think & play more.
-}
