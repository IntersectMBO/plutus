-- In this article we'll show how to define data types in a PlutusIR-like language and describe
-- the problem that arises when we try to construct a generic fold over such data types.
-- This is not a tutorial on how to encode System F-omega in Agda, nor it's a tutorial on
-- generic programming techniques.

-- Since we take denotations of data types that can be impredicative, we need to make Agda
-- impredicative as well.
{-# OPTIONS --type-in-type #-}

module DirectFold where

-- We'll need some administrative stuff (imports, usual data type definitions and functions over them).
-- The actual article starts after
-- "Now that we've defined all the prerequisites, we can proceed to the actual article.",
-- but the prerequisites are commented, so do scroll through them.

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base
open import Data.Product
open import Data.List.Base
open import Data.List.Any

-- | `ifix`. Check `docs/fomega/deep-isorecursive/README.md` for details.
{-# NO_POSITIVITY_CHECK #-}
data IFix {ι φ} {I : Set ι} (F : (I -> Set φ) -> I -> Set φ) (i : I) : Set φ where
  Wrap : F (IFix F) i -> IFix F i

infixr 6 _⇒_ _⇒ᵏ_ _⇒ᶜ_
infixl 7 _∙_
infix  3 _⊢ᵗ_

module Context {α} (A : Set α) where
  infixl 5 _▻_ _▻▻_ _◅▻_
  infix  3 _∈_ _⊆_

  -- | A context is a snoc-list.
  data Con : Set α where
    ε   : Con
    _▻_ : (Γ : Con) -> A -> Con

  -- | Concatenate two contexts.
  _▻▻_ : Con -> Con -> Con
  Γ ▻▻  ε      = Γ
  Γ ▻▻ (Δ ▻ τ) = Γ ▻▻ Δ ▻ τ

  -- | Append the second context to the first one in reverse order.
  _◅▻_ : Con -> Con -> Con
  Γ ◅▻  ε      = Γ
  Γ ◅▻ (Δ ▻ τ) = Γ ▻ τ ◅▻ Δ

  -- | Reverse a context.
  reverseᶜ : Con -> Con
  reverseᶜ Γ = ε ◅▻ Γ

  -- | A variable is a point in a context.
  data _∈_ σ : Con -> Set where
    vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
    vs_ : ∀ {Γ τ} -> (v : σ ∈ Γ) -> σ ∈ Γ ▻ τ

  -- | Expand the context that a variable is defined in, but do not change the variable.
  wkᵛ : ∀ {Γ Δ σ} -> σ ∈ Δ -> σ ∈ Γ ▻▻ Δ
  wkᵛ  vz    = vz
  wkᵛ (vs v) = vs (wkᵛ v)

  -- | Order-preserving embedding. I.e. in `Γ ⊆ Δ` `Δ` contains the same elements as `Γ` and
  -- they're in the same order, but there can be additional elements between them.
  -- See https://fplab.bitbucket.io/posts/2008-03-07-order-preserving-embeddin.html
  data _⊆_ : Con -> Con -> Set where
    stop : ε ⊆ ε
    skip : ∀ {Γ Δ σ} -> (ι : Γ ⊆ Δ) -> Γ     ⊆ Δ ▻ σ
    keep : ∀ {Γ Δ σ} -> (ι : Γ ⊆ Δ) -> Γ ▻ σ ⊆ Δ ▻ σ

  -- | The identity embedding.
  idᵒ : ∀ {Γ} -> Γ ⊆ Γ
  idᵒ {ε}     = stop
  idᵒ {Γ ▻ σ} = keep idᵒ

  -- | Compose two embedding.
  _∘ᵒ_ : ∀ {Γ Δ Ξ} -> Δ ⊆ Ξ -> Γ ⊆ Δ -> Γ ⊆ Ξ
  stop   ∘ᵒ ι      = ι
  skip κ ∘ᵒ ι      = skip (κ ∘ᵒ ι)
  keep κ ∘ᵒ skip ι = skip (κ ∘ᵒ ι)
  keep κ ∘ᵒ keep ι = keep (κ ∘ᵒ ι)

  top : ∀ {Γ σ} -> Γ ⊆ Γ ▻ σ
  top = skip idᵒ

  -- | Rename a variable.
  renᵛ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
  renᵛ  stop     ()
  renᵛ (skip ι)  v     = vs (renᵛ ι v)
  renᵛ (keep ι)  vz    = vz
  renᵛ (keep ι) (vs v) = vs (renᵛ ι v)

  module Environment {β} (_◆_ : Con -> A -> Set β) where
    infix  3 _⊢ᵉ_
    infixl 5 _▷_ _▷▷_ _◁▷_

    -- | In `Δ ⊢ᵉ Γ` there is a `Δ ◆ σ` for each `σ` from `Γ`.
    -- We define `_⊢ᵉ_` by recursion rather than via the `data` keyword, because environments appear
    -- in the denotations of constructor types and this way we can keep them implicit there, because
    -- Agda's unification machinery has some special rules that allow to infer `record`s
    -- (`_×_` is a `record`), but not `data`.
    _⊢ᵉ_ : Con -> Con -> Set β
    Δ ⊢ᵉ ε     = ⊤               -- Type checks only because of --type-in-type.
    Δ ⊢ᵉ Γ ▻ σ = Δ ⊢ᵉ Γ × Δ ◆ σ

    pattern Ø = tt
    pattern _▷_ ρ t = ρ , t

    -- | Concatenate two environments.
    _▷▷_ : ∀ {Ξ Γ Δ} -> Δ ⊢ᵉ Γ -> Δ ⊢ᵉ Ξ -> Δ ⊢ᵉ Γ ▻▻ Ξ
    _▷▷_ {ε}     ρ  Ø      = ρ
    _▷▷_ {_ ▻ _} ρ (χ ▷ t) = ρ ▷▷ χ ▷ t

    -- | Append the second environment to the first one in reverse order.
    _◁▷_ : ∀ {Ξ Γ Δ} -> Δ ⊢ᵉ Γ -> Δ ⊢ᵉ Ξ -> Δ ⊢ᵉ Γ ◅▻ Ξ
    _◁▷_ {ε}     ρ  Ø      = ρ
    _◁▷_ {_ ▻ _} ρ (χ ▷ t) = ρ ▷ t ◁▷ χ

    -- | Reverse an environment.
    reverseᵉ : ∀ {Γ Δ} -> Δ ⊢ᵉ Γ -> Δ ⊢ᵉ reverseᶜ Γ
    reverseᵉ ρ = Ø ◁▷ ρ

    -- | Look up a variable in an environment.
    lookupᵉ : ∀ {Γ Δ σ} -> σ ∈ Γ -> Δ ⊢ᵉ Γ -> Δ ◆ σ
    lookupᵉ  vz    (ρ ▷ t) = t
    lookupᵉ (vs v) (ρ ▷ t) = lookupᵉ v ρ

    -- | Apply a function to the `init` and the `last` of a non-empty environment.
    splitᵉ : ∀ {α Γ Δ σ} {A : Set α} -> (Δ ⊢ᵉ Γ -> Δ ◆ σ -> A) -> Δ ⊢ᵉ Γ ▻ σ -> A
    splitᵉ f (ρ ▷ t) = f ρ t

-- | A `Kind` is either a star or an arrow.
data Kind : Set where
  ⋆    : Kind
  _⇒ᵏ_ : Kind -> Kind -> Kind

open Context Kind renaming (Con to Conᵏ; ε to εᵏ; _▻_ to _▻ᵏ_)

mutual
  -- | Types of kind `⋆`.
  Star : Conᵏ -> Set
  Star Θ = Θ ⊢ᵗ ⋆

  -- | A type is defined in a context and has a kind.
  data _⊢ᵗ_ Θ : Kind -> Set where
    Var : ∀ {σ} -> (v : σ ∈ Θ) -> Θ ⊢ᵗ σ
    Lam : ∀ {σ τ} -> (β : Θ ▻ᵏ σ ⊢ᵗ τ) -> Θ ⊢ᵗ σ ⇒ᵏ τ
    _∙_ : ∀ {σ τ} -> (φ : Θ ⊢ᵗ σ ⇒ᵏ τ) -> (α : Θ ⊢ᵗ σ) -> Θ ⊢ᵗ τ
    _⇒_ : (α : Star Θ) -> (β : Star Θ) -> Star Θ
    π   : ∀ σ -> (β : Star (Θ ▻ᵏ σ)) -> Star Θ
    μ   : ∀ {κ} -> (ψ : Θ ⊢ᵗ (κ ⇒ᵏ ⋆) ⇒ᵏ κ ⇒ᵏ ⋆) -> (α : Θ ⊢ᵗ κ) -> Star Θ

-- | Closed types.
Type⁽⁾ : Kind -> Set
Type⁽⁾ σ = εᵏ ⊢ᵗ σ

-- | Closed types that can be used in any context.
Type⁺ : Kind -> Set
Type⁺ σ = ∀ {Γ} -> Γ ⊢ᵗ σ

-- | Expand the context that a type is defined in, but do not change anything in the type
-- (including variables).
wkᵗ : ∀ {Θ Ξ σ} -> Ξ ⊢ᵗ σ -> Θ ▻▻ Ξ ⊢ᵗ σ
wkᵗ (Var v) = Var (wkᵛ v)
wkᵗ (Lam β) = Lam (wkᵗ β)
wkᵗ (φ ∙ α) = wkᵗ φ ∙ wkᵗ α
wkᵗ (α ⇒ β) = wkᵗ α ⇒ wkᵗ β
wkᵗ (π σ β) = π σ (wkᵗ β)
wkᵗ (μ ψ α) = μ (wkᵗ ψ) (wkᵗ α)

-- | Rename a type.
renᵗ : ∀ {Θ Ξ σ} -> Θ ⊆ Ξ -> Θ ⊢ᵗ σ -> Ξ ⊢ᵗ σ
renᵗ ι (Var v) = Var (renᵛ ι v)
renᵗ ι (Lam β) = Lam (renᵗ (keep ι) β)
renᵗ ι (φ ∙ α) = renᵗ ι φ ∙ renᵗ ι α
renᵗ ι (α ⇒ β) = renᵗ ι α ⇒ renᵗ ι β
renᵗ ι (π σ α) = π σ (renᵗ (keep ι) α)
renᵗ ι (μ ψ α) = μ (renᵗ ι ψ) (renᵗ ι α)

-- | Increase all variables in a type by one.
shiftᵗ : ∀ {Θ σ τ} -> Θ ⊢ᵗ σ -> Θ ▻ᵏ τ ⊢ᵗ σ
shiftᵗ = renᵗ top

-- | Fold a context with `_⇒ᵏ_`.
--
-- > conToKindʳ (εᵏ ▻ σₙ ▻ ... ▻ σ₁) τ = σ₁ ⇒ ... ⇒ σₙ ⇒ τ
conToKindʳ : Conᵏ -> Kind -> Kind
conToKindʳ  εᵏ      τ = τ
conToKindʳ (Θ ▻ᵏ σ) τ = σ ⇒ᵏ conToKindʳ Θ τ

-- Now that we've defined all the prerequisites, we can proceed to the actual article.

{- Note [Type denotations]
The denotation of a System Fω type is an Agda type that somehow corresponds to the original type.
For System Fω types we'll be using simple and straightforward denotations. For example, we map

    π ⋆ (Var vz ⇒ Var vz)

to

    (A : Set) -> A -> A

and

    Lam (Var vz) ∙ (π ⋆ (Var vz ⇒ Var vz))

to the same

    (A : Set) -> A -> A

The latter is due to the fact that we map System Fω lambdas to Agda lambdas and System Fω
applications to Agda applications and hence get type normalization of denotations for free.
-}

{- Note [Kind denotations]
Of course before taking denotations of System Fω types, we need to be able to take denotations
of System Fω kinds. We map a System Fω `⋆` to an Agda `Set` and a `System Fω `_⇒ᵏ_` to an Agda
`_->_`. For example the denotation of

  (⋆ ⇒ᵏ ⋆) ⇒ᵏ ⋆

is

  (Set -> Set) -> Set
-}

-- | The Agda meaning of a kind.
⟦_⟧ᵏ : Kind -> Set
⟦ ⋆      ⟧ᵏ = Set
⟦ σ ⇒ᵏ τ ⟧ᵏ = ⟦ σ ⟧ᵏ -> ⟦ τ ⟧ᵏ

-- The module below defines the machinery that allows to take the Agda denotation of a System Fω type.

module _ where
  -- | Since the meaning of a kind does not depend on the context that a type having this kind is
  -- defined in, we simply ignore contexts here. And since it's not important what context to ignore,
  -- we use `εᵏ ⊢ᵉ Θ` below.
  open Environment (λ _ σ -> ⟦ σ ⟧ᵏ)

  -- | The Agda meaning of a type in an environment.
  evalᵗ : ∀ {Θ σ} -> εᵏ ⊢ᵉ Θ -> Θ ⊢ᵗ σ -> ⟦ σ ⟧ᵏ
  evalᵗ ρ (Var v) = lookupᵉ v ρ                      -- Look up a variable in the current context.
  evalᵗ ρ (Lam β) = λ A -> evalᵗ (ρ ▷ A) β           -- Map a System Fω lambda to an Agda lambda.
  evalᵗ ρ (φ ∙ α) = evalᵗ ρ φ (evalᵗ ρ α)            -- Map a System Fω application to an Agda application.
  evalᵗ ρ (α ⇒ β) = evalᵗ ρ α -> evalᵗ ρ β           -- Map a System Fω arrow to an Agda arrow.
  evalᵗ ρ (π σ β) = (A : ⟦ σ ⟧ᵏ) -> evalᵗ (ρ ▷ A) β  -- Map a System Fω `all` to an Agda `∀`.
  evalᵗ ρ (μ ψ α) = IFix (evalᵗ ρ ψ) (evalᵗ ρ α)     -- Map a System Fω `ifix` to an Agda `IFix`.

  -- | The Agda meaning of a closed type.
  ⟦_⟧ᵗ : ∀ {σ} -> Type⁽⁾ σ -> ⟦ σ ⟧ᵏ
  ⟦_⟧ᵗ = evalᵗ Ø

-- We can now look at a few examples of type denotations.

module EvalTypeExamples where
  -- Check that `all (A :: Set). A -> A` denotes `(A : Set) -> A -> A`.
  test₁
    : ⟦ π ⋆ (Var vz ⇒ Var vz) ⟧ᵗ
    ≡ ((A : Set) -> A -> A)
  test₁ = refl

  -- Check that `(\(B :: *) -> B) (all (A :: *). A -> A)` denotes `(A : Set) -> A -> A` as well.
  test₂
    : ⟦ Lam (Var vz) ∙ π ⋆ (Var vz ⇒ Var vz) ⟧ᵗ
    ≡ ((A : Set) -> A -> A)
  test₂ = refl

  -- A little bit more complicated case.
  test₃
    : ⟦ π (⋆ ⇒ᵏ ⋆) (π ⋆ (π ⋆ (
          (Var (vs vz) ⇒ Var vz) ⇒ Var (vs vs vz) ∙ Var (vs vz) ⇒ Var (vs vs vz) ∙ Var vz
        )))
      ⟧ᵗ
    ≡ ((F : Set -> Set) (A : Set) (B : Set) -> (A -> B) -> F A -> F B)
  test₃ = refl

{- Note [Representing data types]
We represent data types as lists of constructor types. Each constructor type is defined in a
non-empty context where the first bound variable is for handling recursion and other variables are
parameters of the data type (there can be none). Each constructor type is a sequence of `_⇒ᶜ_`
that ends in `endᶜ` where `endᶜ` is a placeholder that will later be substituted either for
a type being defined or a type we eliminate the data type into or the unit type,
depending on how we denote constructors (there are multiple ways).

Consider the `list` data type. Its pattern functor binds two variables:

1. one responsible for recursion
2. one for the type of the elements stored in a list

Since we define constructors in contexts, the list constructors are defined in

    ε ▻ (⋆ ⇒ ⋆) ▻ ⋆

(the parens are for clarity, they're not really needed). The types of the constructors then are

    1. endᶜ                                    -- The type of the `nil` constructor.
    2. Var vz ⇒ᶜ Var (vs vz) ∙ Var vz ⇒ᶜ endᶜ  -- The type of the `cons` constructor.

A more interesting example is

    data InterList (A B : Set) : Set where
      InterNil  : InterList A B
      InterCons : A -> B -> InterList B A -> InterList A B

The types of its constructors are described as

    1. endᶜ
    2. Var (vs vz) ⇒ᶜ Var vz ⇒ᶜ Var (vs vs vz) ∙ Var vz ∙ Var (vs vz) ⇒ᶜ endᶜ

Below we define the data type that describes constructors and some basic functions over it.
-}

-- | The type of a constructor is of the `σ₁ ⇒ ... ⇒ σₙ ⇒ end` form
-- where each `σ` is a type of kind `⋆`.
data Cons Θ : Set where
  endᶜ : Cons Θ
  _⇒ᶜ_ : (α : Star Θ) -> (ξ : Cons Θ) -> Cons Θ

-- | Convert the type of a constructor to an actual type of kind `⋆`.
consToType : ∀ {Θ} -> Cons Θ -> Star Θ -> Star Θ
consToType  endᶜ    β = β
consToType (α ⇒ᶜ ξ) β = α ⇒ consToType ξ β

-- | Rename the type of a constructor.
renᶜ : ∀ {Θ Ξ} -> Θ ⊆ Ξ -> Cons Θ -> Cons Ξ
renᶜ ι  endᶜ    = endᶜ
renᶜ ι (α ⇒ᶜ ξ) = renᵗ ι α ⇒ᶜ renᶜ ι ξ

-- | Increase all variables in the type of a constructor by one.
shiftᶜ : ∀ {Θ τ} -> Cons Θ -> Cons (Θ ▻ᵏ τ)
shiftᶜ = renᶜ top

-- | Take a context, compute the kind of the first variable of an n-ary pattern functor
-- (i.e. the one responsible for recursion) from it, make a singleton context out of the result
-- and append the original context in reverse order to it.
-- The final result is a valid context of an n-ary pattern functor treated as a binder.
--
-- > patternify (εᵏ ▻ σₙ ▻ ... ▻ σ₁) = εᵏ ▻ (σ₁ ⇒ ... ⇒ σₙ ⇒ ⋆) ▻ σ₁ ▻ ... ▻ σₙ
patternify : Conᵏ -> Conᵏ
patternify Θʳ = εᵏ ▻ᵏ conToKindʳ Θʳ ⋆ ◅▻ Θʳ

module _ where
  -- Proving anything about a data type that receives an arbitrary number of arguments is very hard,
  -- because you have to skip those type arguments first and then proceed to the actual proof you
  -- want to write, but that skipping is recursive, i.e. you need to maintain some induction
  -- hypothesis during the skipping and figuring out how it's supposed to look is rather non-trivial.
  -- So instead we do a funny twist that greatly simplifies everything: instead of proving properties
  -- about `D x₁ ... xₙ` where `D` is a data types and `xᵢ`s are its parameters, we prove properties
  -- about `curryᵉ D (x₁ , ... , xₙ)`. I.e. we package the parameters in a tuple and apply the
  -- curries version of `D` to that tuple. Then we prove that there is an inverse of `curryᵉ`,
  -- named `uncurryᵉ`, and eliminate `curryᵉ` via that inverse.

  open Environment (λ _ σ -> ⟦ σ ⟧ᵏ)

  -- | Curry a function that expects an environment. The resulting function receives n type
  -- arguments, packs them into an environment and passed the environment to the original function.
  curryᵉ : ∀ {Θʳ τ} -> (εᵏ ⊢ᵉ Θʳ -> ⟦ τ ⟧ᵏ) -> ⟦ conToKindʳ Θʳ τ ⟧ᵏ
  curryᵉ {εᵏ}      F = F Ø
  curryᵉ {Θʳ ▻ᵏ σ} F = λ A -> curryᵉ (λ ρ -> F (ρ ▷ A))

  -- | Uncurry a function that expects n type arguments. The resulting function receives an
  -- environment and iteratively applies the original function to the elements of the environment.
  uncurryᵉ : ∀ {Θʳ τ} -> ⟦ conToKindʳ Θʳ τ ⟧ᵏ -> εᵏ ⊢ᵉ Θʳ -> ⟦ τ ⟧ᵏ
  uncurryᵉ {εᵏ}     Y  Ø      = Y
  uncurryᵉ {_ ▻ᵏ _} F (ρ ▷ A) = uncurryᵉ (F A) ρ

  -- | A proof that `uncurryᵉ` is the inverse of `curryᵉ`.
  uncurry-curryᵉ : ∀ {Θʳ τ} -> (F : εᵏ ⊢ᵉ Θʳ -> ⟦ τ ⟧ᵏ) -> ∀ ρ -> uncurryᵉ (curryᵉ F) ρ ≡ F ρ
  uncurry-curryᵉ {εᵏ}     F  Ø      = refl
  uncurry-curryᵉ {_ ▻ᵏ _} F (ρ ▷ x) = uncurry-curryᵉ (λ ρ′ -> F (ρ′ ▷ x)) ρ

  uncurry-curry-coeᵉ : ∀ {Θʳ} {F : εᵏ ⊢ᵉ Θʳ -> Set} -> ∀ ρ -> uncurryᵉ (curryᵉ F) ρ -> F ρ
  uncurry-curry-coeᵉ = subst id ∘ uncurry-curryᵉ _

{- Note [Denoting the type of constructors]
To take the denotations of the types of constructors, all we need is to have the name for
the data type being defined in scope and to bound all other context entries via `∀` on
the Agda side. Then we can substitute all the variables appearing in types for what they stand for
and replace each final `endᶜ` by the name of the data type being defined applied to all
the variables bound via `∀`.

For example, recall that the types of constructors of `InterList` are

    1. endᶜ
    2. Var (vs vz) ⇒ᶜ Var vz ⇒ᶜ Var (vs vs vz) ∙ Var vz ∙ Var (vs vz) ⇒ᶜ endᶜ

hence their denotations are

    1. ∀ {A B} -> InterList A B
    2. ∀ {A B} -> A -> B -> InterList B A -> InterList A B
-}

{- Note [Storing data in constructors]
In Note [Denoting the type of constructors] we saw how to denote the type of a constructor.
There a constructor is treated as a function returning the data type that the constructor belongs to.
However there is another way to look at constructors: they're not only functions returning data types,
they also carry some data. The `cons` constructor of `List A` stores an `A` and a `List A`, so its
"carrying" denotation is `A × List A`. Note that this is no longer a function, we do not construct
a data type here, we only say what kind of content the constructor stores.

Of course, there is a strong connection between these two denotations: anything of the same type
that a constructor has can be applied to the actual content that this constructor carries.
This is captured by the `eval-extend` function below (which has a lot of unrelated details).

For Scott-encoding data types, we use the "function" denotation.
For actually storing stuff in constructors, we use the "carrying" denotation.
-}

module _ where
  open Environment (λ _ σ -> ⟦ σ ⟧ᵏ)

  eval-goᶜ : ∀ {Θʳ} -> ⟦ conToKindʳ Θʳ ⋆ ⟧ᵏ -> εᵏ ⊢ᵉ Θʳ -> Cons (patternify Θʳ) -> Set
  eval-goᶜ F ρ  endᶜ    = uncurryᵉ F ρ
  eval-goᶜ F ρ (α ⇒ᶜ ξ) = evalᵗ (Ø ▷ F ◁▷ ρ) α -> eval-goᶜ F ρ ξ

  -- See Note [Denoting the type of constructors].
  -- | Take the denotation of the type of a constructor.
  evalᶜ
    : ∀ {Θʳ}
    -> ⟦ conToKindʳ Θʳ ⋆ ⟧ᵏ  -- ^ The data type being defined.
    -> Cons (patternify Θʳ)  -- ^ The type of a constructor.
    -> Set
  evalᶜ F ξ = ∀ {ρ} -> eval-goᶜ F ρ ξ

  -- See Note [Storing data in constructors].
  -- | Return the type of content that a constructor can store.
  extendᶜ : ∀ {Θ} -> εᵏ ⊢ᵉ Θ -> Cons Θ -> Set
  extendᶜ ρ  endᶜ    = ⊤
  extendᶜ ρ (α ⇒ᶜ ξ) = evalᵗ ρ α × extendᶜ ρ ξ

-- Next goes the main definition.

-- | A data type description is a list of described constructors.
-- A data type is defined in a reversed context, which we then reverse again and prepend an element
-- to it which denotes the variable responsible for recursion. There is no deep theoretical reason
-- why the contexts is reversed, it's simply much easier to deal with, otherwise computing the type
-- of the variable responsible for recursion is harder and extending the context with that variable
-- is harder as well. We could require the user to provide the full context of a pattern functor,
-- but then we would need to check whether the context is of the
--
-- > (k₁ ⇒ ... ⇒ kₙ ⇒ ⋆) ▻ k₁ ▻ ... ▻ kₙ
--
-- form, while here we have correct-by-construction contexts.
record DataType Θʳ : Set where
  constructor PackDataType
  field constructors : List (Cons (patternify Θʳ))

module Direct where
  open Environment (λ _ σ -> ⟦ σ ⟧ᵏ)

  -- See Note [Storing data in constructors].
  -- | The fixed point of a function that picks a constructor of a data type from the list of its
  -- constructors and interprets it in the "carring" way. I.e. the function can be read as
  -- "store some appropriate data in a constructor and if there is a recursive occurrence,
  -- then store there data as well".
  Bodyᵈ : ∀ {Θʳ} -> List (Cons (patternify Θʳ)) -> εᵏ ⊢ᵉ Θʳ -> Set
  Bodyᵈ conses = IFix (λ F ρⁱ -> Any (extendᶜ $ Ø ▷ curryᵉ F ◁▷ ρⁱ) conses)

  -- | The denotation of a data type is basically `Bodyᵈ`, except rather than receiving
  -- an environment, the denotation receives n type arguments and packs them as an environment.
  ⟦_⟧ᵈ : ∀ {Θʳ} -> DataType Θʳ -> ⟦ conToKindʳ Θʳ ⋆ ⟧ᵏ
  ⟦ PackDataType conses ⟧ᵈ = curryᵉ $ Bodyᵈ conses

  -- So now we can describe a data type as a list of constructors defined in some context and
  -- we also can take the denotation of this data type and construct values of this data type
  -- in Agda. We can even prove that the denotation of a data type is isomorphic to this data type
  -- defined in Agda directly. But we can only do this for particular data types
  -- (e.g. see the `toList∘fromList` and `fromList∘toList` proofs below), not generically,
  -- because we can't define data types in the Agda side generically.

  -- What we're interested in, however, is not proving that the current denotations make sense --
  -- we take this as an axiom, because
  --
  -- 1) those denotations are trivial compared to what we get after the translation to System Fω
  -- 2) we do not really have tools for proving such a metatheorem
  --
  -- We're interested in whether it's possible to translate a data type described as a list of
  -- constructors to vanilla System Fω, take the denotation of that (i.e. just call `⟦_⟧ᵗ`) and
  -- prove that the resulting denotation is isomorphic to the denotation of the original description.
  -- But we do not even attempt doing that in this article, because we fail quickly without diving
  -- into any particular details of the translation.

  -- In order to define a translation we at the very least need a function that takes a value of the
  -- denotation of a list-of-constructors data type and turns it into a value of the denotation of
  -- this data type encoded as a vanilla System Fω type (we also need a function that works the
  -- other way around and proofs that those two functions are inverses of each other).
  -- Such function is basically a fold over a list-of-constructors data type. Arguments of this fold
  -- are constructors of the encoded data type. We do not have encoded data types in this article,
  -- but all this mapping mechanics remains the same everywhere and we can look at examples with
  -- native Agda data types instead:
  --
  -- 1) see `toList` for an inlined fold
  -- 2) see `toInterList` for an example with an actual fold

  -- Therefore, we need generic folds over list-of-constructors data types. This is not a problem
  -- for simple data types like lists. But in our PlutusIR-like language we allow much more than
  -- that, we even allow types of constructors to be non-normalized. Since the process of taking
  -- any denotation of a data type also implies normalization of everything along the way,
  -- converting between denotations becomes very hard, because you have to think about reductions.
  -- And the type language of System Fω is essentially simply-typed lambda calculus, so our
  -- situation is that we need to convert values of complicated types and recursive cases can be
  -- literally anywhere there. You can have a recursive case deep inside some another data structure
  -- wrapped into several redexes. You can bind a recursive case to a variable and distribute it
  -- using whatever STLC-term you can come up with. And now you need to convert a value of such
  -- data type in a type-driven way to something else, where "type-driven" means that you need to
  -- match on the structure of types with all the lambdas, function applications and foralls they
  -- can contain and figure out what to next by just looking at this non-normalized syntax.

  -- This does not normally happen in generic programming where you either know precisely where
  -- recursive cases are or just don't care about them at all and use type classes to handle them.
  -- The type class approach is a convenient one, but it's not a fair type-driven translation:
  -- it's just saying "ok, compiler will compute everything for some particular data type and
  -- realize how to handle the result", but it does not mean a compiler can't eventually say
  -- "oh, I do not know how to handle this particular case". Practically, it's fine. Theoretically,
  -- it's the same thing as not proving that you can convert one data types to another at all.

  -- Below go elaborations on these problems and a suggested solution, but basically the type
  -- language of a PlutusIR-like language is way too expressive and proving generic properties
  -- about PlutusIR-like data types does not look feasible without restricting the type language.

  -- | This is the problem that ruins everything. This function is needed below, but it's just
  -- impossible to define it, even though it says something very natural. Namely, that a value of
  -- a type interpreted in one environment can be converted to some value of the same type
  -- interpreted in the same environment with its first element changed (i.e. the one that handles
  -- recursive cases), provided there is a way to convert original recursive case handler to
  -- the new one. The problem is that we not only have arbitrary System F-omega types here and need
  -- to dig through them in order to figure out how to convert terms (pretty much like we do that
  -- in Observational Type Theory), but we also allow arbitrary Agda types in environments!
  -- That's certainly too much, we can have a recursive case like `List F` (think of rose trees)
  -- with `List` being in the environment and converting `List F` to `List G` requires us to know
  -- the internal structure of `List`, which we don't know here, because this function is
  -- way too abstract.
  --
  -- "Okay, so allow only those types in environments that are denotations of System F-omega types?"
  -- Nope, our problems only start here. Those are really arbitrary System F-omega types,
  -- they can be non-normalized, how do we handle that? Do we need to reduce types during
  -- conversion and then somehow unreduce them back? That sounds undoable.
  -- "Okay, so allow only normalized types in the syntax?"
  -- Nope, during type evaluation we replace variables with Agda types they stand for, meaning
  -- we still get redexes that we don't know how to handle.
  -- "Okay, so put some working suggestion into the mouth of your imaginary comrade?".
  -- Sure: "Okay, so restrict the recursive case to always appear in the head of the outermost
  -- application?" Yep, that should work, because even though it does imply that redexes may appear,
  -- we have this handy function that specifies how to convert a `uncurryᵉ F χ` to a `uncurryᵉ G χ`
  -- for any χ` regardless of whether there are any redexes or not.
  -- This immediately disallows the rose trees examples, although it can be recovered
  -- with the Indexed Functors (Andres Löh & José Pedro Magalhães) trick, but we are not writing
  -- a PhD thesis here, so we won't do that.
  --
  -- What this all means is that it's really hard to construct a conversion from the direct
  -- denotation of a described data type to the denotation of this data type after we encode it
  -- in a System F-omega compatible way. This all does not mean it's hard to encode data types
  -- in a System F-omega compatible way -- the encoding itself is fairly trivial.
  --
  -- And I haven't yet started deriving actual constructors of encoded data types.
  -- And yes, since we do not impose the strict positivity restriction, in order to convert from
  -- direct denotations to denotations of encoded data types, we need to know how to define
  -- a conversion in the opposite direction. And vice versa. I.e. the back and forth conversion
  -- functions have to be mutually recursive.
  postulate
    map-eval-reverse
      : ∀ {Θʳ} {F G : ⟦ conToKindʳ Θʳ ⋆ ⟧ᵏ}
      -> (∀ χ -> uncurryᵉ F χ -> uncurryᵉ G χ)
      -> (ρ : εᵏ ⊢ᵉ Θʳ)
      -> ∀ α
      -> evalᵗ (reverseᵉ (ρ ▷ F)) α
      -> evalᵗ (reverseᵉ (ρ ▷ G)) α

  -- See Note [Storing data in constructors].
  -- | Apply a function that has the same type as the denotation of the `ξ` constructor
  -- to the content stored in this constructor. The recursive case is distinct in the denotations:
  -- it's `G` in the former one and `F` in the latter one, but one of the arguments fills this gap.
  eval-extend
    : ∀ {Θʳ} {F G : ⟦ conToKindʳ Θʳ ⋆ ⟧ᵏ}
    -> (∀ χ -> uncurryᵉ F χ -> uncurryᵉ G χ)  -- ^ The gap filler.
    -> (ρ : εᵏ ⊢ᵉ Θʳ)
    -> ∀ ξ
    -> eval-goᶜ G ρ ξ
    -> extendᶜ ((Ø ▷ F) ◁▷ ρ) ξ
    -> uncurryᵉ G ρ
  eval-extend coe ρ  endᶜ    ev  tt      = ev
  eval-extend coe ρ (α ⇒ᶜ ξ) ev (x , ex) = eval-extend coe ρ ξ (ev (map-eval-reverse coe ρ α x)) ex

  -- | The resulting type of `foldᵈ`.
  --
  -- > FoldResᵀ R ρ [ξ₁, ... , ξₙ] = evalᶜ R ξ₁ -> ... -> evalᶜ R ξₙ -> uncurryᵉ R ρ
  FoldResᵀ : ∀ {Θʳ} -> ⟦ conToKindʳ Θʳ ⋆ ⟧ᵏ -> εᵏ ⊢ᵉ Θʳ -> List (Cons (patternify Θʳ)) -> Set
  FoldResᵀ R ρ = foldr (λ ξ Z -> evalᶜ R ξ -> Z) (uncurryᵉ R ρ)

  BodyFoldᵀ
    : ∀ {Θʳ}
    -> List (Cons (patternify Θʳ)) -> List (Cons (patternify Θʳ)) -> ⟦ conToKindʳ Θʳ ⋆ ⟧ᵏ -> Set
  BodyFoldᵀ allConses remConses R = ∀ {ρ} -> Bodyᵈ allConses ρ -> FoldResᵀ R ρ remConses

  extendBody : ∀ {Θʳ} -> List (Cons (patternify Θʳ)) -> εᵏ ⊢ᵉ Θʳ -> Cons (patternify Θʳ) -> Set
  extendBody allCs ρ = extendᶜ (Ø ▷ curryᵉ (Bodyᵈ allCs) ◁▷ ρ)

  {-# TERMINATING #-}  -- Lie.
  fold-goᵈ : ∀ {Θʳ} {R : ⟦ conToKindʳ Θʳ ⋆ ⟧ᵏ} -> ∀ allCs -> BodyFoldᵀ allCs allCs R
  fold-goᵈ {R = R} allCs {ρ} (Wrap el) = pre (fold-goᵈ allCs) el where
    post
      : ∀ {allCs ξ}
      -> ∀ remCs -> BodyFoldᵀ allCs remCs R -> extendBody allCs ρ ξ -> evalᶜ R ξ -> FoldResᵀ R ρ remCs
    post  []         k ex ev₀ = eval-extend (λ χ x -> k (uncurry-curry-coeᵉ χ x)) ρ _ ev₀ ex
    post (_ ∷ remCs) k ex ev₀ = λ ev -> post remCs (λ a -> k a ev) ex ev₀

    pre
      : ∀ {remCs allCs}
      -> BodyFoldᵀ allCs remCs R -> Any (extendBody allCs ρ) remCs -> FoldResᵀ R ρ remCs
    pre {_ ∷ remCs} k (here  ex) = λ ev -> post remCs (λ a -> k a ev) ex ev
    pre             k (there el) = λ ev -> pre (λ a -> k a ev) el

  foldᵈ = λ {Θʳ ρ R} (dataType : DataType Θʳ) (x : uncurryᵉ ⟦ dataType ⟧ᵈ ρ) ->
    fold-goᵈ {R = R} (DataType.constructors dataType) (uncurry-curry-coeᵉ ρ x)

module ExamplesDirect where
  module ListExample where
    list : DataType (εᵏ ▻ᵏ ⋆)
    list
      = PackDataType
      $ endᶜ
      ∷ Var vz ⇒ᶜ Var (vs vz) ∙ Var vz ⇒ᶜ endᶜ
      ∷ []

    List′ : Set -> Set
    List′ = Direct.⟦ list ⟧ᵈ

    pattern []′       = Wrap (here tt)
    pattern _∷′_ x xs = Wrap (there (here (x , xs , tt)))
    pattern ⟨⟩₂       = Wrap (there (there ()))

    fromList : ∀ {A} -> List A -> List′ A
    fromList  []      = []′
    fromList (x ∷ xs) = x ∷′ fromList xs

    toList : ∀ {A} -> List′ A -> List A
    toList  []′      = []
    toList (x ∷′ xs) = x ∷ toList xs
    toList  ⟨⟩₂

    toList∘fromList : ∀ {A} -> (xs : List A) -> toList (fromList xs) ≡ xs
    toList∘fromList  []      = refl
    toList∘fromList (x ∷ xs) = cong (x ∷_) (toList∘fromList xs)

    fromList∘toList : ∀ {A} -> (xs : List′ A) -> fromList (toList xs) ≡ xs
    fromList∘toList  []′      = refl
    fromList∘toList (x ∷′ xs) = cong (x ∷′_) (fromList∘toList xs)
    fromList∘toList  ⟨⟩₂

  module InterListExample where
    data InterList (A B : Set) : Set where
      InterNil  : InterList A B
      InterCons : A -> B -> InterList B A -> InterList A B

    interlist : DataType (εᵏ ▻ᵏ ⋆ ▻ᵏ ⋆)
    interlist
      = PackDataType
      $ endᶜ
      ∷ Var (vs vz) ⇒ᶜ Var vz ⇒ᶜ Var (vs vs vz) ∙ Var vz ∙ Var (vs vz) ⇒ᶜ endᶜ
      ∷ []

    InterList′ : Set -> Set -> Set
    InterList′ = Direct.⟦ interlist ⟧ᵈ

    pattern InterNil′          = Wrap (here tt)
    pattern InterCons′ x y yxs = Wrap (there (here (x , y , yxs , tt)))
    pattern ⟨⟩′                = Wrap (there (there ()))

    fromInterList : ∀ {A B} -> InterList A B -> InterList′ A B
    fromInterList  InterNil           = InterNil′
    fromInterList (InterCons x y yxs) = InterCons′ x y $ fromInterList yxs

    toInterList : ∀ {A B} -> InterList′ A B -> InterList A B
    toInterList xys = Direct.foldᵈ interlist xys InterNil InterCons
