{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Examples.Data.Rose
    (
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.MkPlc

import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.Unit
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

    open import Data.Unit.Base
    open import Data.Sum.Base
    open import Data.Product

    TreeForest : Set -> (Set -> Set -> Set) -> Set
    TreeForest =
      Fix₂ λ R A tag ->
        let Tree   a = R a (λ (T F : Set) -> T)
            Forest a = R a (λ (T F : Set) -> F)
          in tag
               (A × Forest A)
               (⊤ ⊎ Tree A × Forest A)

    Tree : Set -> Set
    Tree A = TreeForest A (λ (T F : Set) -> T)

    Forest : Set -> Set
    Forest A = TreeForest A (λ (T F : Set) -> F)
-}
