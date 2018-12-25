{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}

module Language.PlutusCore.Examples.Data.TreeForest
    ( getBuiltinTree
    , getBuiltinForest
    , getBuiltinTreeNode
    , getBuiltinForestNil
    , getBuiltinForestCons
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Normalize

import           Language.PlutusCore.StdLib.Type

{- Note [Tree]
Here we encode the following:

    mutual
      data Tree (A : Set) : Set where
        node : A -> Forest A -> Tree A

      data Forest (A : Set) : Set where
        nil  : Forest A
        cons : Tree A -> Forest A -> Forest A

    mutual
      mapTree : ∀ A B -> (A -> B) -> Tree A -> Tree B
      mapTree A B f (node x forest) = node (f x) (mapForest A B f forest)

      mapForest : ∀ A B -> (A -> B) -> Forest A -> Forest B
      mapForest A B f  nil               = nil
      mapForest A B f (cons rose forest) = cons (mapTree A B f rose) (mapForest A B f forest)

using this representation:

    {-# OPTIONS --type-in-type #-}

    {-# NO_POSITIVITY_CHECK #-}
    data IFix {A : Set} (F : (A -> Set) -> A -> Set) (x : A) : Set where
      wrap : F (IFix F) x -> IFix F x

    Fix₂ : ∀ {A B} -> ((A -> B -> Set) -> A -> B -> Set) -> A -> B -> Set
    Fix₂ F x y = IFix (λ B P -> P (F λ x y -> B λ R -> R x y)) (λ R -> R x y)

    treeTag : Set -> Set -> Set
    treeTag T F = T

    forestTag : Set -> Set -> Set
    forestTag T F = F

    AsTree : (Set -> (Set -> Set -> Set) -> Set) -> Set -> Set
    AsTree D A = D A treeTag

    AsForest : (Set -> (Set -> Set -> Set) -> Set) -> Set -> Set
    AsForest D A = D A forestTag

    TreeForest : Set -> (Set -> Set -> Set) -> Set
    TreeForest =
      Fix₂ λ Rec A tag ->
        ∀ R -> tag ((A -> AsForest Rec A -> R) -> R) (R -> (AsTree Rec A -> AsForest Rec A -> R) -> R)

    Tree : Set -> Set
    Tree = AsTree TreeForest

    Forest : Set -> Set
    Forest = AsForest TreeForest
-}

infixr 5 ~~>

class HasArrow a where
    (~~>) :: a -> a -> a

instance a ~ () => HasArrow (Kind a) where
    (~~>) = KindArrow ()

instance a ~ () => HasArrow (Type tyname a) where
    (~~>) = TyFun ()

star :: Kind ()
star = Type ()

getTreeTag :: Quote (Type TyName ())
getTreeTag = do
    t <- freshTyName () "t"
    f <- freshTyName () "f"
    return
        . TyLam () t star
        . TyLam () f star
        $ TyVar () t

getForestTag :: Quote (Type TyName ())
getForestTag = do
    t <- freshTyName () "t"
    f <- freshTyName () "f"
    return
        . TyLam () t star
        . TyLam () f star
        $ TyVar () f

getAsTree :: Quote (Type TyName ())
getAsTree = do
    treeTag <- getTreeTag
    d <- freshTyName () "d"
    a <- freshTyName () "a"
    return
        . TyLam () d (star ~~> (star ~~> star ~~> star) ~~> star)
        . TyLam () a star
        $ mkIterTyApp () (TyVar () d)
            [ TyVar () a
            , treeTag
            ]

getAsForest :: Quote (Type TyName ())
getAsForest = do
    forestTag <- getForestTag
    d <- freshTyName () "d"
    a <- freshTyName () "a"
    return
        . TyLam () d (star ~~> (star ~~> star ~~> star) ~~> star)
        . TyLam () a star
        $ mkIterTyApp () (TyVar () d)
            [ TyVar () a
            , forestTag
            ]

getBuiltinTreeForest :: Quote (RecursiveType ())
getBuiltinTreeForest = do
    asTree     <- getAsTree
    asForest   <- getAsForest
    treeForest <- freshTyName () "treeForest"
    a          <- freshTyName () "a"
    r          <- freshTyName () "r"
    tag        <- freshTyName () "tag"
    let vA = TyVar () a
        vR = TyVar () r
        recSpine = [TyVar () treeForest, vA]
    let tree   = mkIterTyApp () asTree   recSpine
        forest = mkIterTyApp () asForest recSpine
    body <- rename
        . TyForall () r (Type ())
        $ mkIterTyApp () (TyVar () tag)
            [ (vA ~~> forest ~~> vR) ~~> vR
            , vR ~~> (tree ~~> forest ~~> vR) ~~> vR
            ]
    makeRecursiveType () treeForest
        [TyVarDecl () a star, TyVarDecl () tag $ star ~~> star ~~> star]
        body

getBuiltinTree :: Quote (RecursiveType ())
getBuiltinTree = do
    RecursiveType treeForest wrapTreeForest <- getBuiltinTreeForest
    treeTag <- getTreeTag
    asTree  <- getAsTree
    let tree = TyApp () asTree treeForest
    return $ RecursiveType tree (\[a] -> wrapTreeForest [a, treeTag])

getBuiltinForest :: Quote (RecursiveType ())
getBuiltinForest = do
    RecursiveType treeForest wrapTreeForest <- getBuiltinTreeForest
    forestTag <- getForestTag
    asForest  <- getAsForest
    let forest = TyApp () asForest treeForest
    return $ RecursiveType forest (\[a] -> wrapTreeForest [a, forestTag])

-- |
--
-- > /\(a :: *) -> \(x : a) (fr : forest a) ->
-- >     wrapTree [a] /\(r :: *) -> \(f : a -> forest a -> r) -> f x fr
getBuiltinTreeNode :: Quote (Term TyName Name ())
getBuiltinTreeNode = runNormalizeTypeDownM . normalizeTypesIn =<< rename =<< do
    RecursiveType _      wrapTree <- getBuiltinTree
    RecursiveType forest _        <- getBuiltinForest
    a  <- freshTyName () "a"
    r  <- freshTyName () "r"
    x  <- freshName () "x"
    fr <- freshName () "fr"
    f  <- freshName () "f"
    let vA = TyVar () a
        vR = TyVar () r
    Normalized forestA <- normalizeTypeDown $ TyApp () forest vA
    return
        . TyAbs () a (Type ())
        . LamAbs () x vA
        . LamAbs () fr forestA
        . wrapTree [vA]
        . TyAbs () r (Type ())
        . LamAbs () f (mkIterTyFun () [vA, forestA] vR)
        $ mkIterApp () (Var () f)
            [ Var () x
            , Var () fr
            ]
-- |
--
-- > /\(a :: *) ->
-- >     wrapForest [a] /\(r :: *) -> \(z : r) (f : tree a -> forest a -> r) -> z
getBuiltinForestNil :: Quote (Term TyName Name ())
getBuiltinForestNil = runNormalizeTypeDownM . normalizeTypesIn =<< rename =<< do
    RecursiveType tree   _          <- getBuiltinTree
    RecursiveType forest wrapForest <- getBuiltinForest
    a <- freshTyName () "a"
    r <- freshTyName () "r"
    z <- freshName () "z"
    f <- freshName () "f"
    let vA = TyVar () a
        vR = TyVar () r
    Normalized treeA   <- normalizeTypeDown $ TyApp () tree   vA
    Normalized forestA <- normalizeTypeDown $ TyApp () forest vA
    return
        . TyAbs () a (Type ())
        . wrapForest [vA]
        . TyAbs () r (Type ())
        . LamAbs () z vR
        . LamAbs () f (mkIterTyFun () [treeA, forestA] vR)
        $ Var () z

-- |
--
-- > /\(a :: *) -> \(tr : tree a) (fr : forest a)
-- >     wrapForest [a] /\(r :: *) -> \(z : r) (f : tree a -> forest a -> r) -> f tr fr
getBuiltinForestCons :: Quote (Term TyName Name ())
getBuiltinForestCons = runNormalizeTypeDownM . normalizeTypesIn =<< rename =<< do
    RecursiveType tree   _          <- getBuiltinTree
    RecursiveType forest wrapForest <- getBuiltinForest
    a  <- freshTyName () "a"
    tr <- freshName () "tr"
    fr <- freshName () "fr"
    r  <- freshTyName () "r"
    z  <- freshName () "z"
    f  <- freshName () "f"
    let vA = TyVar () a
        vR = TyVar () r
    Normalized treeA   <- normalizeTypeDown $ TyApp () tree   vA
    Normalized forestA <- normalizeTypeDown $ TyApp () forest vA
    return
        . TyAbs () a (Type ())
        . LamAbs () tr treeA
        . LamAbs () fr forestA
        . wrapForest [vA]
        . TyAbs () r (Type ())
        . LamAbs () z vR
        . LamAbs () f (mkIterTyFun () [treeA, forestA] vR)
        $ mkIterApp () (Var () f)
            [ Var () tr
            , Var () fr
            ]
