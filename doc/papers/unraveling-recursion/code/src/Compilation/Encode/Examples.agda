{-# OPTIONS --type-in-type #-}

module Compilation.Encode.Examples where

open import Context
open import Type.Core
open import Compilation.Data
open import Compilation.Encode.Core

open import Function
open import Data.Product
open import Data.List.Base

module ProdTreeTreeExample where
  open ProdTreeTree
  open prodTreeTree

  ProdTreeTree′ = ⟦ prodTreeTree ⟧ᵈ

  ProdTree′ : Set -> Set -> Set
  ProdTree′ with ProdTreeTree′
  ... | ø ▶ PT′ ▶ T′ = PT′

  Tree′ : Set -> Set
  Tree′ with ProdTreeTree′
  ... | ø ▶ PT′ ▶ T′ = T′

  mutual
    fromProdTree : ∀ {A B A′ B′} -> (A -> A′) -> (B -> B′) -> ProdTree A B -> ProdTree′ A′ B′
    fromProdTree f g (Prod tree) =
      Wrap λ R h -> h $ fromTree (λ{ (x , y) _ k -> k (f x) (g y) }) tree

    fromTree : ∀ {A A′} -> (A -> A′) -> Tree A -> Tree′ A′
    fromTree f (Leaf x)    = Wrap λ R g h -> g $ f x
    fromTree f (Fork prod) = Wrap λ R g h -> h $ fromProdTree f f prod

  {-# TERMINATING #-}
  mutual
    toProdTree : ∀ {A B A′ B′} -> (A -> A′) -> (B -> B′) -> ProdTree′ A B -> ProdTree A′ B′
    toProdTree f g (Wrap k) =
      k _ λ tree -> Prod $ toTree (λ k -> k _ λ x y -> f x , g y) tree

    toTree : ∀ {A A′} -> (A -> A′) -> Tree′ A -> Tree A′
    toTree f (Wrap k) = k _ (Leaf ∘ f) (Fork ∘ toProdTree f f)

module ListExample where
  list : Data⁺ (ε ▻ (ε ▻ ⋆))
  list
    = PackData
    $ ø
    ▶ ( endᶜ
      ∷ Var vz ⇒ᶜ Var (vs vz) ∙ Var vz ⇒ᶜ endᶜ
      ∷ []
      )

  List′ : Set -> Set
  List′ with ⟦ list ⟧ᵈ
  ... | ø ▶ L′ = L′

  fromList : ∀ {A} -> List A -> List′ A
  fromList  []      = Wrap λ R z f -> z
  fromList (x ∷ xs) = Wrap λ R z f -> f x $ fromList xs

  {-# TERMINATING #-}
  toList : ∀ {A} -> List′ A -> List A
  toList (Wrap k) = k _ [] λ x xs -> x ∷ toList xs

module InterListExample where
  data InterList (A B : Set) : Set where
    InterNil  : InterList A B
    InterCons : A -> B -> InterList B A -> InterList A B

  interlist : Data⁺ (ε ▻ (ε ▻ ⋆ ▻ ⋆))
  interlist
    = PackData
    $ ø
    ▶ ( endᶜ
      ∷ Var (vs vz) ⇒ᶜ Var vz ⇒ᶜ Var (vs vs vz) ∙ Var vz ∙ Var (vs vz) ⇒ᶜ endᶜ
      ∷ []
      )

  InterList′ : Set -> Set -> Set
  InterList′ with ⟦ interlist ⟧ᵈ
  ... | ø ▶ IL′ = IL′

  fromInterList : ∀ {A B} -> InterList A B -> InterList′ A B
  fromInterList  InterNil           = Wrap λ R z f -> z
  fromInterList (InterCons x y yxs) = Wrap λ R z f -> f x y $ fromInterList yxs

  {-# TERMINATING #-}
  toInterList : ∀ {A B} -> InterList′ A B -> InterList A B
  toInterList (Wrap k) = k _ InterNil λ x y yxs -> InterCons x y $ toInterList yxs

module TreeForestExample where
  mutual
    data Tree (A : Set) : Set where
      node : A -> Forest A -> Tree A

    data Forest (A : Set) : Set where
      nil  : Forest A
      cons : Tree A -> Forest A -> Forest A

  treeForest : Data⁺ (ε ▻ (ε ▻ ⋆) ▻ (ε ▻ ⋆))
  treeForest
    = PackData
    $ ø
    ▶ ( Var vz ⇒ᶜ Var (vs vz) ∙ Var vz ⇒ᶜ endᶜ
      ∷ []
      )
    ▶ ( endᶜ
      ∷ Var (vs vs vz) ∙ Var vz ⇒ᶜ Var (vs vz) ∙ Var vz ⇒ᶜ endᶜ
      ∷ []
      )

  TreeForest′ = ⟦ treeForest ⟧ᵈ

  Tree′ : Set -> Set
  Tree′ with TreeForest′
  ... | ø ▶ T′ ▶ F′ = T′

  Forest′ : Set -> Set
  Forest′ with TreeForest′
  ... | ø ▶ T′ ▶ F′ = F′

  mutual
    fromTree : ∀ {A} -> Tree A -> Tree′ A
    fromTree (node x forest) = Wrap λ R f -> f x $ fromForest forest

    fromForest : ∀ {A} -> Forest A -> Forest′ A
    fromForest  nil               = Wrap λ R z f -> z
    fromForest (cons tree forest) = Wrap λ R z f -> f (fromTree tree) (fromForest forest)

  {-# TERMINATING #-}
  mutual
    toTree : ∀ {A} -> Tree′ A -> Tree A
    toTree (Wrap k) = k _ λ x forest -> node x $ toForest forest

    toForest : ∀ {A} -> Forest′ A -> Forest A
    toForest (Wrap k) = k _ nil λ tree forest -> cons (toTree tree) (toForest forest)

module MNExample where
  mutual
    data M (A : Set) : Set where
      p : A -> M A
      n : N -> M A

    data N : Set where
      m : M N -> N

  mn : Data⁺ (ε ▻ (ε ▻ ⋆) ▻ ε)
  mn
    = PackData
    $ ø
    ▶ ( Var vz ⇒ᶜ endᶜ
      ∷ Var (vs vz) ⇒ᶜ endᶜ
      ∷ []
      )
    ▶ ( Var (vs vz) ∙ Var vz ⇒ᶜ endᶜ
      ∷ []
      )

  MN′ = ⟦ mn ⟧ᵈ

  M′ : Set -> Set
  M′ with MN′
  ... | ø ▶ M′ ▶ N′ = M′

  N′ : Set
  N′ with MN′
  ... | ø ▶ M′ ▶ N′ = N′

  {-# TERMINATING #-}
  mutual
    fromM : ∀ {A B} -> (A -> B) -> M A -> M′ B
    fromM f (p x) = Wrap λ R g h -> g $ f x
    fromM f (n x) = Wrap λ R g h -> h $ fromN x

    fromN : N -> N′
    fromN (m x) = Wrap λ R f -> f $ fromM fromN x

  {-# TERMINATING #-}
  mutual
    toM : ∀ {A B} -> (A -> B) -> M′ A -> M B
    toM f (Wrap k) = k _ (λ x -> p (f x)) (λ x -> n (toN x))

    toN : N′ -> N
    toN (Wrap k) = k _ λ x -> m (toM toN x)
