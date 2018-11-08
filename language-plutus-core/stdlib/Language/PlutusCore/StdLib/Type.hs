-- | This module defines Haskell data types that simplify construction of PLC types and terms.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.StdLib.Type
    ( RecursiveType (..)
    , makeRecursiveType
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Quote
import           PlutusPrelude

import           Data.Traversable          (for)

infixr 5 ~~>

(~~>) :: Kind () -> Kind () -> Kind ()
(~~>) = KindArrow ()

star :: Kind ()
star = Type ()

getToPatternFunctor :: Kind () -> Quote (Type TyName ())
getToPatternFunctor k = rename =<< do
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
--
-- > FixN : ∀ {K} -> (((K -> Set) -> Set) -> K) -> (K -> K) -> K
-- > FixN {K} withSpine Pat =
-- >     withSpine λ (spine : K -> Set) -> IFix patternFunctor spine where
-- >         patternFunctor = λ (B : (K -> Set) -> Set) (P : K -> Set) -> P (Pat (withSpine B))
getTyFixN :: Kind () -> Quote (Type TyName ())
getTyFixN k = rename =<< do
    withSpine        <- freshTyName () "withSpine"
    pat              <- freshTyName () "pat"
    toPatternFunctor <- getToPatternFunctor k
    spine            <- freshTyName () "spine"

    return
        . TyLam () withSpine (((k ~~> star) ~~> star) ~~> k)
        . TyLam () pat (k ~~> k)
        . TyApp () (TyVar () withSpine)
        . TyLam () spine (k ~~> star)
        $ TyIFix ()
            (mkIterTyApp () toPatternFunctor [TyVar () withSpine, TyVar () pat])
            (TyVar () spine)

-- > Fix₀ : (Set -> Set) -> Set
-- > Fix₀ = FixN withSpine0 where
-- >     withSpine0 =
-- >         λ (K : (Set -> Set) -> Set) ->
-- >             K λ (R : Set) -> R

-- | > toRecKind _ [k1, k2 ... kn] = k1 -> k2 -> ... -> kn -> *
toRecKind :: ann -> [Kind ann] -> Kind ann
toRecKind ann kindArgs = mkIterKindArrow ann kindArgs $ Type ann

-- |
--
-- > getSpine _ [a1 :: k1, a2 :: k2 ... an :: kn] =
-- >     \(R :: k1 -> k2 -> ... kn -> *) -> R a1 a2 ... an
--
-- E.g.
--
-- > getSpine _ [a1 :: k1, a2 :: k2] =
-- >     \(R :: k1 -> k2 -> *) -> R a1 a2
getSpine :: ann -> [TyDecl TyName ann] -> Quote (Type TyName ann)
getSpine ann args = do
    r <- freshTyName ann "r"

    return
        . TyLam ann r (toRecKind ann $ map tyDeclKind args)
        . mkIterTyApp ann (TyVar ann r)
        $ map tyDeclType args

-- |
--
-- > getWithSpine [k1, k2 ... kn] =
-- >     \(K :: (((k1 -> k2 -> ... -> kn -> *) -> *) -> *)
-- >      (a1 :: k1) (a2 :: k2) ... (an :: kn) ->
-- >          K \(R :: k1 -> k2 -> ... kn -> *) -> R a1 a2 ... an
--
-- E.g.
--
-- > getWithSpine [k1, k2] =
-- >     \(K : ((k1 -> k2 -> *) -> *) -> *) (a1 :: k1) (a2 :: k2) ->
-- >          K \(R :: k1 -> k2 -> *) -> R a1 a2
getWithSpine :: ann -> [Kind ann] -> Quote (Type TyName ann)
getWithSpine ann argKinds = rename =<< do
    k <- freshTyName ann "k"
    args <- for (zip [1 :: Int ..] argKinds) $ \(argN, argKind) -> do
        name <- freshTyNameText ann $ "a" <> prettyText argN
        return $ TyVarDecl ann name argKind
    spine <- getSpine ann $ map tyDeclVar args

    return
        . TyLam ann k (KindArrow ann (KindArrow ann (toRecKind ann argKinds) $ Type ann) $ Type ann)
        . mkIterTyLam ann args
        . TyApp ann (TyVar ann k)
        $ spine

closeBody :: ann -> TyName ann -> Type TyName ann -> [Kind ann] -> Type TyName ann
closeBody ann name patBody argKinds = TyLam ann name (toRecKind ann argKinds) patBody

getTyFix :: ann -> TyName ann -> Type TyName ann -> [Kind ann] -> Quote (Type TyName ann)
getTyFix ann name patBody argKinds = rename =<< do
    withSpine <- getWithSpine ann argKinds
    let pat = closeBody ann name patBody argKinds
    tyFixN <- getTyFixN . void $ toRecKind ann argKinds
    return $ mkIterTyApp ann (ann <$ tyFixN) [withSpine, pat]

getWrap
    :: a
    -> TyName a
    -> Type TyName a
    -> [TyDecl TyName a]
    -> Term TyName Name a
    -> Quote (Term TyName Name a)
getWrap ann name patBody args term = rename =<< do
    let argKinds = map tyDeclKind args
    withSpine <- getWithSpine ann argKinds
    let pat = closeBody ann name patBody argKinds
    toPatternFunctor <- getToPatternFunctor . void $ toRecKind ann argKinds
    spine <- getSpine ann args
    return $ IWrap ann (mkIterTyApp ann (ann <$ toPatternFunctor) [withSpine, pat]) spine term

-- | A 'Type' that starts with a 'TyFix' (i.e. a recursive type) packaged along with a
-- specified 'Wrap' that allows to construct elements of this type.
data RecursiveType = RecursiveType
    { _recursiveWrap :: [Type TyName ()] -> Term TyName Name () -> Quote (Term TyName Name ())
    , _recursiveType :: Type TyName ()
    }

makeRecursiveType
    :: TyName ()
    -> [Kind ()]
    -> ((Type TyName () -> Quote (Type TyName ())) -> Quote (Type TyName ()))
    -> Quote RecursiveType
makeRecursiveType name argKinds cont = do
    fixedPat <- cont $ \pat -> getTyFix () name pat argKinds
    let wrap args term =
            cont return >>= \patBind ->
                getWrap () name patBind (zipWith (TyDecl ()) args argKinds) term
    return $ RecursiveType wrap fixedPat
