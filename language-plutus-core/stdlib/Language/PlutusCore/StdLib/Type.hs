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
getToPatternFunctor k = do
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
getTyFixN k = do
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

getToSpine :: ann -> Quote ([TyDecl TyName ann] -> Type TyName ann)
getToSpine ann = do
    r <- freshTyName ann "r"

    return $ \args ->
          TyLam ann r (toRecKind ann $ map tyDeclKind args)
        . mkIterTyApp ann (TyVar ann r)
        $ map tyDeclType args

-- |
--
-- > getSpine _ [a1 :: k1, a2 :: k2 ... an :: kn] =
-- >     \(R :: k1 -> k2 -> ... kn -> *) -> R a1 a2 ... an
--
-- For example
--
-- > getSpine _ [a1 :: k1, a2 :: k2] =
-- >     \(R :: k1 -> k2 -> *) -> R a1 a2
getSpine :: ann -> [TyDecl TyName ann] -> Quote (Type TyName ann)
getSpine ann args = ($ args) <$> getToSpine ann

-- |
--
-- > getWithSpine [k1, k2 ... kn] =
-- >     \(K :: (((k1 -> k2 -> ... -> kn -> *) -> *) -> *)
-- >      (a1 :: k1) (a2 :: k2) ... (an :: kn) ->
-- >          K \(R :: k1 -> k2 -> ... kn -> *) -> R a1 a2 ... an
--
-- For example
--
-- > getWithSpine [k1, k2] =
-- >     \(K : ((k1 -> k2 -> *) -> *) -> *) (a1 :: k1) (a2 :: k2) ->
-- >          K \(R :: k1 -> k2 -> *) -> R a1 a2
getWithSpine :: ann -> [Kind ann] -> Quote (Type TyName ann)
getWithSpine ann argKinds = do
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

packagePatternBodyN
    :: (Kind () -> Quote (Type TyName ()))
       -- ^ Some type-level function that receives @withSpine@ and a pattern functor that binds
       -- @n + 1@ type variables (where @1@ represents the variable responsible for recursion)
       -- using type-level lambdas.
    -> ann              -- ^ An annotation placed everywhere we do not have annotations.
    -> TyName ann       -- ^ The name for the @1@ varible responsible for recursion.
    -> [Kind ann]       -- ^ A list of kinds for @n@ type variables.
    -> Type TyName ann  -- ^ The body of a pattern functor that consequently binds type variables.
    -> Quote (Type TyName ann)
packagePatternBodyN getFun ann name argKinds patBody = do
    withSpine <- getWithSpine ann argKinds
    let pat = TyLam ann name (toRecKind ann argKinds) patBody
    fun <- getFun . void $ toRecKind ann argKinds
    return $ mkIterTyApp ann (ann <$ fun) [withSpine, pat]

getTyFix :: ann -> TyName ann -> [Kind ann] -> Type TyName ann -> Quote (Type TyName ann)
getTyFix = packagePatternBodyN getTyFixN

getWrap
    :: ann
    -> TyName ann
    -> [Kind ann]
    -> Type TyName ann
    -> Quote ([Type TyName ann] -> Term TyName Name ann -> Term TyName Name ann)
getWrap ann name argKinds patBody = do
    pat1 <- packagePatternBodyN getToPatternFunctor ann name argKinds patBody
    toSpine <- getToSpine ann
    -- TODO: check lengths match.
    return $ IWrap ann pat1 . toSpine . zipWith (flip $ TyDecl ann) argKinds

-- | A 'Type' that starts with a 'TyFix' (i.e. a recursive type) packaged along with a
-- specified 'Wrap' that allows to construct elements of this type.
data RecursiveType ann = RecursiveType
    { _recursiveType :: Type TyName ann
      -- ^ This is not supposed to have duplicate names.
    , _recursiveWrap :: [Type TyName ann] -> Term TyName Name ann -> Term TyName Name ann
      -- ^ This produces terms with duplicate names.
    }

makeRecursiveType
    :: ann
    -> TyName ann
    -> [Kind ann]
    -> Type TyName ann
    -> Quote (RecursiveType ann)
makeRecursiveType ann name argKinds patBody =
    RecursiveType <$> getTyFix ann name argKinds patBody <*> getWrap ann name argKinds patBody
