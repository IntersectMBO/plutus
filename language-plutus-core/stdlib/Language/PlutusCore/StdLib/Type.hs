-- | This module defines Haskell data types that simplify construction of PLC types and terms.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}

module Language.PlutusCore.StdLib.Type
    ( (~~>)
    , star
    , RecursiveType (..)
    , makeRecursiveType
    ) where

import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           PlutusPrelude

-- | A 'Type' that starts with a 'TyIFix' (i.e. a recursive type) packaged along with a
-- specified 'Wrap' that allows to construct elements of this type.
data RecursiveType ann = RecursiveType
    { _recursiveType :: Type TyName ann
      -- ^ This is not supposed to have duplicate names.
    , _recursiveWrap :: [Type TyName ann] -> Term TyName Name ann -> Term TyName Name ann
      -- ^ This produces terms with duplicate names.
    }

data IndicesLengthsMismatchError = IndicesLengthsMismatchError
    { _indicesLengthsMismatchErrorExpected :: Int
    , _indicesLengthsMismatchErrorActual   :: Int
    , _indicesLengthsMismatchErrorTyName   :: TyName ()
    } deriving (Typeable)

instance Show IndicesLengthsMismatchError where
    show (IndicesLengthsMismatchError expected actual tyName) = concat
        [ "Wrong number of elements\n"
        , "expected: ", show expected, " , actual: ", show actual, "\n"
        , "while constructing a ", prettyPlcDefString tyName
        ]

instance Exception IndicesLengthsMismatchError

infixr 5 ~~>

class HasArrow a where
    (~~>) :: a -> a -> a

instance a ~ () => HasArrow (Kind a) where
    (~~>) = KindArrow ()

instance a ~ () => HasArrow (Type tyname a) where
    (~~>) = TyFun ()

star :: Kind ()
star = Type ()

-- > \(withSpine :: ((k -> *) -> *) -> k) (pat :: k -> k) ->
-- >     \(b :: (k -> *) -> *) (p :: k -> *) -> p (pat (withSpine b))
getPatternFunctor :: ann -> Type TyName ann -> Type TyName ann -> Kind ann -> Quote (Type TyName ann)
getPatternFunctor ann withSpine pat k = do
    b <- freshTyName ann "b"
    p <- freshTyName ann "p"
    let star  = Type ann
        (~~>) = KindArrow ann

    return
        . TyLam ann b ((k ~~> star) ~~> star)
        . TyLam ann p (k ~~> star)
        . TyApp ann (TyVar ann p)
        . TyApp ann pat
        . TyApp ann withSpine
        $ TyVar ann b

-- |
--
-- > FixN : ∀ {K} -> (((K -> Set) -> Set) -> K) -> (K -> K) -> K
-- > FixN {K} withSpine Pat =
-- >     withSpine λ (spine : K -> Set) -> IFix patternFunctor spine where
-- >         patternFunctor = λ (B : (K -> Set) -> Set) (P : K -> Set) -> P (Pat (withSpine B))
getTyFixN :: ann -> Type TyName ann -> Type TyName ann -> Kind ann -> Quote (Type TyName ann)
getTyFixN ann withSpine pat k = do
    patF  <- getPatternFunctor ann withSpine pat k
    spine <- freshTyName ann "spine"
    let star  = Type ann
        (~~>) = KindArrow ann

    return
        . TyApp ann withSpine
        . TyLam ann spine (k ~~> star)
        $ TyIFix ann patF (TyVar ann spine)

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
-- > getWithSpine [v1 :: k1, v2 :: k2 ... vn :: kn] =
-- >     \(K :: (((k1 -> k2 -> ... -> kn -> *) -> *) -> *)
-- >      (v1 :: k1) (v2 :: k2) ... (vn :: kn) ->
-- >          K \(R :: k1 -> k2 -> ... kn -> *) -> R v1 v2 ... vn
--
-- For example
--
-- > getWithSpine [a1 :: k1, a2 :: k2] =
-- >     \(K : ((k1 -> k2 -> *) -> *) -> *) (a1 :: k1) (a2 :: k2) ->
-- >          K \(R :: k1 -> k2 -> *) -> R a1 a2
getWithSpine :: ann -> [TyVarDecl TyName ann] -> Quote (Type TyName ann)
getWithSpine ann argVars = do
    k <- freshTyName ann "k"
    spine <- getSpine ann $ map tyDeclVar argVars
    let argKinds = map tyVarDeclKind argVars

    return
        . TyLam ann k (KindArrow ann (KindArrow ann (toRecKind ann argKinds) $ Type ann) $ Type ann)
        . mkIterTyLam ann argVars
        . TyApp ann (TyVar ann k)
        $ spine

packagePatternBodyN
    :: (ann -> Type TyName ann -> Type TyName ann -> Kind ann -> Quote (Type TyName ann))
       -- ^ Some type-level function that receives @withSpine@ and a pattern functor that binds
       -- @n + 1@ type variables (where @1@ represents the variable responsible for recursion)
       -- using type-level lambdas.
    -> ann                     -- ^ An annotation placed everywhere we do not have annotations.
    -> TyName ann              -- ^ The name for the @1@ varible responsible for recursion.
    -> [TyVarDecl TyName ann]  -- ^ A list of @n@ type variables.
    -> Type TyName ann         -- ^ The body of a pattern functor
                               -- to which the @n + 1@ type variables will be added via 'TyLam's.
    -> Quote (Type TyName ann)
packagePatternBodyN getFun ann name argVars patBody = do
    withSpine <- getWithSpine ann argVars
    let argKinds = map tyVarDeclKind argVars
        vR  = TyVarDecl ann name $ toRecKind ann argKinds
        pat = mkIterTyLam ann (vR : argVars) patBody
    getFun ann withSpine pat $ toRecKind ann argKinds

getTyFix :: ann -> TyName ann -> [TyVarDecl TyName ann] -> Type TyName ann -> Quote (Type TyName ann)
getTyFix = packagePatternBodyN getTyFixN

getWrap
    :: ann
    -> TyName ann
    -> [TyVarDecl TyName ann]
    -> Type TyName ann
    -> Quote ([Type TyName ann] -> Term TyName Name ann -> Term TyName Name ann)
getWrap ann name argVars patBody = do
    pat1 <- packagePatternBodyN getPatternFunctor ann name argVars patBody
    toSpine <- getToSpine ann
    let instVar var ty = TyDecl ann ty $ tyVarDeclKind var
    return $ \args ->
        let argVarsLen = length argVars
            argsLen = length args
            in if argVarsLen == argsLen
                then IWrap ann pat1 . toSpine $ zipWith instVar argVars args
                else throw . IndicesLengthsMismatchError argVarsLen argsLen $ void name

makeRecursiveType
    :: ann
    -> TyName ann
    -> [TyVarDecl TyName ann]
    -> Type TyName ann
    -> Quote (RecursiveType ann)
makeRecursiveType ann name argVars patBody =
    RecursiveType <$> getTyFix ann name argVars patBody <*> getWrap ann name argVars patBody
