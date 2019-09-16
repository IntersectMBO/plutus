{-# OPTIONS --type-in-type #-}

module Compilation.Data where

open import Context
open import Type.Core

open import Function
open import Data.Product
open import Data.List.Base

infixr 6 _⇒ᶜ_

{- Note [Type denotations]
The denotation of a System Fωμ type is an Agda type that somehow corresponds to the original type.
For System Fωμ types we'll be using simple and straightforward denotations. For example, we map

    π ⋆ (Var vz ⇒ Var vz)

to

    (A : Set) -> A -> A

and

    Lam (Var vz) ∙ (π ⋆ (Var vz ⇒ Var vz))

to

    (λ x -> x) ((A : Set) -> A -> A)

which computes to

    (A : Set) -> A -> A

The latter is due to the fact that we map System Fωμ lambdas to Agda lambdas and System Fωμ
applications to Agda applications and hence get type normalization of denotations for free.
-}

{- Note [Kind denotations]
Of course before taking denotations of System Fωμ types, we need to be able to take denotations
of System Fωμ kinds. We map a System Fωμ `⋆` to an Agda `Set` and a System Fωμ `_⇒ᵏ_` to an Agda
`_->_`. For example the denotation of

  (⋆ ⇒ᵏ ⋆) ⇒ᵏ ⋆

is

  (Set -> Set) -> Set
-}

-- | The Agda meaning of a kind.
⟦_⟧ᵏ : Kind -> Set
⟦ ⋆      ⟧ᵏ = Set
⟦ σ ⇒ᵏ τ ⟧ᵏ = ⟦ σ ⟧ᵏ -> ⟦ τ ⟧ᵏ

-- | The Agda meaning of a System Fωμ type in an environment.
evalᵗ : ∀ {Θ σ} -> Env ⟦_⟧ᵏ Θ -> Θ ⊢ᵗ σ -> ⟦ σ ⟧ᵏ
evalᵗ ρ (Var v) = lookupᵉ v ρ                      -- Look up a variable in the current context.
evalᵗ ρ (Lam β) = λ A -> evalᵗ (ρ ▷ A) β           -- Map a System Fωμ lambda to an Agda lambda.
evalᵗ ρ (φ ∙ α) = evalᵗ ρ φ (evalᵗ ρ α)            -- Map a System Fωμ application to an Agda application.
evalᵗ ρ (α ⇒ β) = evalᵗ ρ α -> evalᵗ ρ β           -- Map a System Fωμ arrow to an Agda arrow.
evalᵗ ρ (π σ β) = (A : ⟦ σ ⟧ᵏ) -> evalᵗ (ρ ▷ A) β  -- Map a System Fωμ `all` to an Agda `∀`.
evalᵗ ρ (μ ψ α) = IFix (evalᵗ ρ ψ) (evalᵗ ρ α)     -- Map a System Fωμ `ifix` to an Agda `IFix`.

-- | The Agda meaning of a closed System Fωμ type.
⟦_⟧ᵗ : ∀ {σ} -> Type⁽⁾ σ -> ⟦ σ ⟧ᵏ
⟦_⟧ᵗ = evalᵗ ∅

{- Note [Representing data types]
We represent a single data type as a list of constructor types. Each constructor type is defined in
a non-empty context where the first bound variable is for handling recursion and other variables are
parameters of the data type (there can be none). Each constructor type is a sequence of `_⇒ᶜ_`
that ends in `endᶜ` where `endᶜ` is a placeholder that will later be substituted either for
a type being defined or a type we eliminate the data type into or the unit type,
depending on how we denote constructors (there are multiple ways).

Consider the `list` data type. Its pattern functor binds two variables:

1. one responsible for recursion
2. one for the type of the elements stored in a list

Since we define constructors in contexts, the list constructors are defined in

    ε ▻ (⋆ ⇒ ⋆) ▻ ⋆

(the parens are for clarity, they're not really needed). The types of the constructors are

    1. List A                 -- The type of the `nil` constructor.
    2. A -> List A -> List A  -- The type of the `cons` constructor.

and we translate them to

    1. endᶜ
    2. Var vz ⇒ᶜ Var (vs vz) ∙ Var vz ⇒ᶜ endᶜ

A more interesting example is

    data InterList (A B : Set) : Set where
      InterNil  : InterList A B
      InterCons : A -> B -> InterList B A -> InterList A B

The types of its constructors are described as

    1. endᶜ
    2. Var (vs vz) ⇒ᶜ Var vz ⇒ᶜ Var (vs vs vz) ∙ Var vz ∙ Var (vs vz) ⇒ᶜ endᶜ

Below we define the data type that describes constructors and some basic functions over it.
-}

-- | The type of a constructor is of the `σ₁ ⇒ … ⇒ σₙ ⇒ end` form
-- where each `σ` is a type of kind `⋆`.
data Cons Θ : Set where
  endᶜ : Cons Θ
  _⇒ᶜ_ : (α : Star Θ) -> (ξ : Cons Θ) -> Cons Θ

-- | Convert the type of a constructor to an actual type of kind `⋆`.
--
-- > consToType (α₁ ⇒ᶜ … ⇒ᶜ αₙ ⇒ᶜ endᶜ) β = α₁ ⇒ … ⇒ αₙ ⇒ β
consToType : ∀ {Θ} -> Cons Θ -> Star Θ -> Star Θ
consToType  endᶜ    β = β
consToType (α ⇒ᶜ ξ) β = α ⇒ consToType ξ β

-- | Rename the type of a constructor.
renᶜ : ∀ {Θ Ξ} -> Θ ⊆ Ξ -> Cons Θ -> Cons Ξ
renᶜ ι  endᶜ    = endᶜ
renᶜ ι (α ⇒ᶜ ξ) = renᵗ ι α ⇒ᶜ renᶜ ι ξ

-- The family we use as an example in docs below.
module ProdTreeTree where
  mutual
    data ProdTree (A : Set) (B : Set) : Set where
      Prod : Tree (A × B) -> ProdTree A B

    data Tree (A : Set) : Set where
      Leaf : A -> Tree A
      Fork : ProdTree A A -> Tree A

  open import Data.Nat.Base
  open import Data.Bool.Base

  private
    example : ProdTree ℕ Bool
    example
      = Prod ∘ Fork ∘ Prod ∘ Fork ∘ Prod ∘ Leaf
      $ ( ( 0
          , false
          )
        , ( 1
          , true
          )
        )
      , ( ( 2
          , false
          )
        , (3
          , true
          )
        )

-- | A data description is parameterized by a context of contexts of kinds. Inner contexts are those
-- single data types are defined in. Outer contexts are needed in order to allow to define mutually
-- recursive data types. I.e. each element of an outer context is an inner context, in which
-- a single data type is defined.
--
-- A single data type is described as a list of described constructors. The context of each
-- constructor consists of
--
--   1. all the data types being defined (because we allow mutually recursive data types)
--   2. the particular inner context of the data type that the constructor constructs
--
-- For example, consider the `ProdTree`/`Tree` family of data types defined above
--
-- Since there are two data types in this family, the length of the outer context is 2.
-- Since `ProdTree` is parameterized by two types, it's inner context is `ε ▻ ⋆ ▻ ⋆`.
-- Since `Tree` is parameterized by one type, it's inner context is `ε ▻ ⋆`.
-- I.e. the context this whole family is defined in, is
--
-- > ε ▻ (ε ▻ ⋆ ▻ ⋆) ▻ (ε ▻ ⋆)
--
-- The context that the constructor of `ProdTree` is defined in, consists of
--
--     1. References to both `ProdTree` and `Tree` which have the `⋆ ⇒ᵏ ⋆ ⇒ᵏ ⋆` and  `⋆ ⇒ᵏ ⋆`
--        kinds respectively.
--     2. The inner context of `ProdTree` which has two parameters `A` and `B`, each of kind `⋆`.
--
-- hence the final context is
--
-- > ε ▻ {- ProdTree :: -} (⋆ ⇒ᵏ ⋆ ⇒ᵏ ⋆) ▻ {- Tree :: -} (⋆ ⇒ᵏ ⋆) ▻ {- A :: -} ⋆ ▻ {- B :: -} ⋆
--
-- (things in `{- … -}` are comments that assign names to variables for clarity).
--
-- Analogously, the context that the constructors of Tree` are defined in, is
--
-- > ε ▻ {- ProdTree :: -} (⋆ ⇒ᵏ ⋆ ⇒ᵏ ⋆) ▻ {- Tree :: -} (⋆ ⇒ᵏ ⋆) ▻ {- A :: -} ⋆
--
-- I.e. the same as the one of `ProdTree`, except we bind only one type parameter, because `Tree`
-- has only one type parameter.
record Data Ξ (Θs : Con Conᵏ) : Set where
  constructor PackData
  field constructors : Seq (λ Θ -> List (Cons (Ξ ▻▻ mapᶜ (λ Θᵢ -> conToKind Θᵢ ⋆) Θs ▻▻ Θ))) Θs

Data⁺ : Con Conᵏ -> Set
Data⁺ Θs = ∀ {Ξ} -> Data Ξ Θs

module prodTreeTree where
  -- The encoded `ProdTree`/`Tree` family from the above looks like this:
  -- (`∀ Q -> (A -> B -> Q) -> Q` is the Scott-encoded `A × B`)
  prodTreeTree : Data⁺ (ε ▻ (ε ▻ ⋆ ▻ ⋆) ▻ (ε ▻ ⋆))
  prodTreeTree
    = PackData
    $ ø
    ▶ ( -- `Tree (∀ Q -> (A -> B -> Q) -> Q) -> ProdTree A B`
        Var (vs vs vz) ∙ π ⋆ ((Var (vs vs vz) ⇒ Var (vs vz) ⇒ Var vz) ⇒ Var vz) ⇒ᶜ endᶜ
      ∷ []
      )
    ▶ ( -- `A -> Tree A`
        Var vz ⇒ᶜ endᶜ
      ∷ -- `ProdTree A A -> Tree A`
        Var (vs vs vz) ∙ Var vz ∙ Var vz ⇒ᶜ endᶜ
      ∷ []
      )
