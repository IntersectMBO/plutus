-- | This module defines Haskell data types that simplify construction of PLC types and terms.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.StdLib.Type
    ( RecursiveType (..)
    , makeRecursiveType
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.MkPlc
import           PlutusPrelude

infixr 5 ~~>

(~~>) :: Kind () -> Kind () -> Kind ()
(~~>) = KindArrow ()

star :: Kind ()
star = Type ()

getPatternFunctor :: Kind () -> Quote (Type TyName ())
getPatternFunctor k = rename =<< do
    withSpine <- freshTyName () "withSpine"
    pat       <- freshTyName () "pat"
    b         <- freshTyName () "b"
    p         <- freshTyName () "p"

    return
        . TyLam () withSpine (((k ~~> star) ~~> star) ~~> k)
        . TyLam () pat (k ~~> k)
        . TyLam () b ((k ~~> star) ~~> star)
        . TyLam () p (k ~~> star)
        . TyApp () (TyVar () p)
        . TyApp () (TyVar () pat)
        . TyApp () (TyVar () withSpine)
        $ TyVar () b

-- |
-- > FixN : ∀ {K} -> (((K -> Set) -> Set) -> K) -> (K -> K) -> K
-- > FixN {K} withSpine Pat =
-- >     withSpine λ (spine : K -> Set) -> IFix patternFunctor spine where
-- >         patternFunctor = λ (B : (K -> Set) -> Set) (P : K -> Set) -> P (Pat (withSpine B))
getTyFixN :: Kind () -> Quote (Type TyName ())
getTyFixN k = rename =<< do
    withSpine      <- freshTyName () "withSpine"
    pat            <- freshTyName () "pat"
    patternFunctor <- getPatternFunctor k
    spine          <- freshTyName () "spine"

    return
        . TyLam () withSpine (((k ~~> star) ~~> star) ~~> k)
        . TyLam () pat (k ~~> k)
        . TyApp () (TyVar () withSpine)
        . TyLam () spine (k ~~> star)
        $ TyIFix ()
            (mkIterTyApp () patternFunctor [TyVar () withSpine, TyVar () pat])
            (TyVar () spine)

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
getTyFix0 ann name patBind = rename =<< do
    withSpine0 <- getWithSpine0
    let pat = TyLam () (void name) star (void patBind)
    tyFixN <- getTyFixN star

    -- First throw away annotations, then annotate everything using the same annotation. Silly.
    return $ ann <$ mkIterTyApp () tyFixN [withSpine0, pat]

-- IWrap (λ B P -> P (Pat (B (λ R -> R)))) (λ R -> R)
getWrap :: a -> TyName a -> Type TyName a -> Term TyName Name a -> Quote (Term TyName Name a)
getWrap ann name patBind term = rename =<< do
    withSpine0 <- getWithSpine0
    let pat = TyLam () (void name) star (void patBind)
    patternFunctor <- getPatternFunctor star

    -- TODO: generalize for other cases.
    identity <- do
        r <- freshTyName () "r"
        return
            . TyLam () r star
            $ TyVar () r

    return $ IWrap ann (ann <$ mkIterTyApp () patternFunctor [withSpine0, pat]) (ann <$ identity) term

-- | A 'Type' that starts with a 'TyFix' (i.e. a recursive type) packaged along with a
-- specified 'Wrap' that allows to construct elements of this type.
data RecursiveType = RecursiveType
    { _recursiveWrap :: Term TyName Name () -> Quote (Term TyName Name ())
    , _recursiveType :: Type TyName ()
    }

makeRecursiveType
    :: TyName ()
    -> ((Type TyName () -> Quote (Type TyName ())) -> Quote (Type TyName ()))
    -> Quote RecursiveType
makeRecursiveType name cont = do
    let wrap term = cont return >>= \ty -> getWrap () name ty term
    fixedPat <- cont $ getTyFix0 () name
    return $ RecursiveType wrap fixedPat
