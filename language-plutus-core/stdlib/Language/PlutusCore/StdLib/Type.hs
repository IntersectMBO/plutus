-- | This module defines Haskell data types that simplify construction of PLC types and terms.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.StdLib.Type
    ( HoledType(..)
    , RecursiveType(..)
    , holedTyApp
    , holedToRecursive
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Renamer
import           PlutusPrelude

infixr 5 ~~>

(~~>) :: Kind () -> Kind () -> Kind ()
(~~>) = KindArrow ()

star :: Kind ()
star = Type ()

getPatternFunctor
    :: Kind ()
    -> Type TyName ()
    -> Type TyName ()
    -> Quote (Type TyName ())
getPatternFunctor k withSpine pat = rename =<< do
    b <- freshTyName () "b"
    p <- freshTyName () "p"

    -- TODO: return
    --     . TyLam () withSpine (((k ~~> star) ~~> star) ~~> k)
    --     . TyLam () pat (k ~~> k)

    return
        . TyLam () b ((k ~~> star) ~~> star)
        . TyLam () p (k ~~> star)
        . TyApp () (TyVar () p)
        . TyApp () pat
        . TyApp () withSpine
        $ TyVar () b

-- |
-- > FixN : ∀ {K} -> (((K -> Set) -> Set) -> K) -> (K -> K) -> K
-- > FixN {K} withSpine Pat =
-- >     withSpine λ (spine : K -> Set) -> IFix patternFunctor spine where
-- >         patternFunctor = λ (B : (K -> Set) -> Set) (P : K -> Set) -> P (Pat (withSpine B))
getTyFixN
    :: Kind ()
    -> Type TyName ()
    -> Type TyName ()
    -> Quote (Type TyName ())
getTyFixN k withSpine pat = rename =<< do
    patternFunctor <- getPatternFunctor k withSpine pat
    spine          <- freshTyName () "spine"

    return
        . TyApp () withSpine
        . TyLam () spine (k ~~> star)
        $ TyIFix () patternFunctor (TyVar () spine)

getWithSpine0 :: Quote (Type TyName ())
getWithSpine0 = rename =<< do
    k <- freshTyName () "k"
    r <- freshTyName () "r"

    return
        . TyLam () k ((star ~~> star) ~~> star)
        . TyApp () (TyVar () k)
        . TyLam () r star
        $ TyVar () r

-- |
-- > Fix₀ : (Set -> Set) -> Set
-- > Fix₀ = FixN withSpine0 where
-- >     withSpine0 =
-- >         λ (K : (Set -> Set) -> Set) ->
-- >             K λ (R : Set) -> R
getTyFix0 :: a -> TyName a -> Type TyName a -> Quote (Type TyName a)
getTyFix0 ann name patBind = do
    withSpine0 <- getWithSpine0
    let pat = TyLam () (void name) star (void patBind)

    -- First throw away annotations, then annotate everything using the same annotation. Silly.
    (ann <$) <$> getTyFixN star withSpine0 pat

-- IWrap (λ B P -> P (Pat (B (λ R -> R)))) (λ R -> R)
getWrap :: a -> TyName a -> Type TyName a -> Quote (Term TyName Name a -> Term TyName Name a)
getWrap ann name patBind = do
    withSpine0 <- getWithSpine0
    let pat = TyLam () (void name) star (void patBind)
    patternFunctor <- getPatternFunctor star withSpine0 pat

    -- TODO: generalize for other cases.
    identity <- do
        r <- freshTyName () "r"
        return
            . TyLam () r star
            $ TyVar () r

    return $ IWrap ann (ann <$ patternFunctor) (ann <$ identity)

-- | A type with a hole inside. The reason for having such a thing is that 'Wrap'
-- expects the pattern functor of a recursive type while in type signatures we use
-- actual recursive types. So we need a way to construct recursive types such that from
-- any such type we can easily extract its pattern functor as well as easily use the
-- type itself. 'RecursiveType' below allows to do that (except the pattern functor is
-- already supplied to 'Wrap'), but some types are actually type functions that receive
-- arguments and only then return a recursive type (see 'getBuiltinList' for example).
-- Thus we make a type with a hole where the hole can be filled by either 'TyFix' or
-- 'id', so this type, after all arguments are supplied (see 'holedTyApp'), can be
-- converted to the corresponding 'RecursiveType' (see 'holedToRecursive').
-- See "docs/Holed types.md" for more information.
data HoledType a = HoledType
    { _holedTypeName :: TyName a
    , _holedTypeCont :: (Type TyName a -> Quote (Type TyName a)) -> Quote (Type TyName a)
    }

-- | A 'Type' that starts with a 'TyFix' (i.e. a recursive type) packaged along with a
-- specified 'Wrap' that allows to construct elements of this type.
data RecursiveType a = RecursiveType
    { _recursiveWrap :: Term TyName Name a -> Term TyName Name a
    , _recursiveType :: Type TyName a
    }

-- | Apply a 'HoledType' to a 'Type'.
holedTyApp :: HoledType () -> Type TyName () -> HoledType ()
holedTyApp (HoledType name cont) arg = HoledType name $ \hole -> TyApp () <$> cont hole <*> pure arg

-- | Convert a 'HoledType' to the corresponding 'RecursiveType'.
holedToRecursive :: HoledType () -> Quote (RecursiveType ())
holedToRecursive (HoledType name cont) = do
    wrap <- getWrap () name =<< cont return
    fixedPat <- cont $ getTyFix0 () name
    return $ RecursiveType wrap fixedPat
