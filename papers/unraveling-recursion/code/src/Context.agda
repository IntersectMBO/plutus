module Context where

open import Level using (_⊔_)
open import Function
open import Data.List.Base

-- | `ifix`. Check `docs/fomega/deep-isorecursive/README.md` for details.
{-# NO_POSITIVITY_CHECK #-}
data IFix {ι φ} {I : Set ι} (F : (I -> Set φ) -> I -> Set φ) (i : I) : Set φ where
  Wrap : F (IFix F) i -> IFix F i

infix  3 _∈_ _⊆_
infixl 5 _▻_ _▻▻_ _▶_ _▷_

-- | A context is a snoc-list.
data Con {α} (A : Set α) : Set α where
  ε   : Con A
  _▻_ : (Γ : Con A) -> A -> Con A

-- | The left fold over a context. Note that for contexts, the left fold is the lazy one,
-- i.e. it's preferable.
foldlᶜ : ∀ {α ρ} {A : Set α} {R : Set ρ} -> (R -> A -> R) -> R -> Con A -> R
foldlᶜ f z  ε      = z
foldlᶜ f z (Γ ▻ σ) = f (foldlᶜ f z Γ) σ

-- | Concatenate two contexts.
_▻▻_ : ∀ {α} {A : Set α} -> Con A -> Con A -> Con A
Γ ▻▻ Δ = foldlᶜ _▻_ Γ Δ
{-# DISPLAY foldlᶜ _▻_ Γ Δ = Γ ▻▻ Δ #-}

-- | The right fold over a context. Note that for contexts, the right fold is the strict one,
-- i.e. it's not preferable.
foldrᶜ : ∀ {α ρ} {A : Set α} {R : Set ρ} -> (A -> R -> R) -> R -> Con A -> R
foldrᶜ f z  ε      = z
foldrᶜ f z (Γ ▻ σ) = foldrᶜ f (f σ z) Γ

-- | Mapping over a context.
mapᶜ : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> Con A -> Con B
mapᶜ f = foldlᶜ (λ Ξ x -> Ξ ▻ f x) ε

joinᶜ : ∀ {α} {A : Set α} -> Con (Con A) -> Con A
joinᶜ = foldlᶜ _▻▻_ ε

listToCon : ∀ {α} {A : Set α} -> List A -> Con A
listToCon = foldl _▻_ ε
{-# DISPLAY foldl _▻_ ε = listToCon #-}

-- | A variable is a point in a context.
data _∈_ {α} {A : Set α} σ : Con A -> Set where
  vz  : ∀ {Γ}   -> σ ∈ Γ ▻ σ
  vs_ : ∀ {Γ τ} -> (v : σ ∈ Γ) -> σ ∈ Γ ▻ τ

-- | Expand the context that a variable is defined in, but do not change the variable.
wkᵛ : ∀ {α} {A : Set α} {Γ Δ : Con A} {σ} -> σ ∈ Δ -> σ ∈ Γ ▻▻ Δ
wkᵛ  vz    = vz
wkᵛ (vs v) = vs (wkᵛ v)

-- | A variable in the middle of a context.
vsⁿ : ∀ {α} {A : Set α} {Θ : Con A} {σ} Ξ -> σ ∈ Θ ▻ σ ▻▻ Ξ
vsⁿ  ε      = vz
vsⁿ (Ξ ▻ ν) = vs (vsⁿ Ξ)

mapᵛ : ∀ {α β} {A : Set α} {B : Set β} {Γ σ} {f : A -> B} -> σ ∈ Γ -> f σ ∈ mapᶜ f Γ
mapᵛ  vz    = vz
mapᵛ (vs v) = vs (mapᵛ v)

-- -- | Order-preserving embedding. I.e. in `Γ ⊆ Δ` `Δ` contains the same elements as `Γ` and
-- -- they're in the same order, but there can be additional elements between them.
-- -- See https://fplab.bitbucket.io/posts/2008-03-07-order-preserving-embeddin.html
-- data _⊆_ {α} {A : Set α} : Con A -> Con A -> Set where
--   -- We use this instead of `ε ⊆ ε`, because we this definition we have `idᵒ ∘ᵒ idᵒ ≡ idᵒ`
--   -- definitionally and this is needed in order to type check some terms with open types.
--   stop : ∀ {Γ}     ->                Γ         ⊆ Γ
--   skip : ∀ {Γ Δ σ} -> (ι : Γ ⊆ Δ) -> Γ         ⊆ Δ ▻ σ
--   keep : ∀ {Γ Δ σ} -> (ι : Γ ⊆ Δ) -> Γ ▻ σ     ⊆ Δ ▻ σ

_⊆_ : ∀ {α} {A : Set α} -> Con A -> Con A -> Set α
Γ ⊆ Δ = ∀ {σ} -> σ ∈ Γ -> σ ∈ Δ

stop : ∀ {α} {A : Set α} {Γ : Con A} -> Γ ⊆ Γ
stop = id

dupl : ∀ {α} {A : Set α} {Γ : Con A} {σ} -> Γ ▻ σ ▻ σ ⊆ Γ ▻ σ
dupl  vz    = vz
dupl (vs v) = v

skip : ∀ {α} {A : Set α} {Γ Δ : Con A} {σ} -> Γ ⊆ Δ -> Γ ⊆ Δ ▻ σ
skip ι = vs_ ∘ ι

keep : ∀ {α} {A : Set α} {Γ Δ : Con A} {σ} -> Γ ⊆ Δ -> Γ ▻ σ ⊆ Δ ▻ σ
keep ι  vz    = vz
keep ι (vs v) = vs (ι v)

move : ∀ {α} {A : Set α} {Γ Δ : Con A} {σ} -> Γ ⊆ Δ -> Γ ▻ σ ▻ σ ⊆ Δ ▻ σ
move ι  vz    = vz
move ι (vs v) = keep ι v

skipⁿ : ∀ {α} {A : Set α} {Γ Δ : Con A} Ξ -> Γ ⊆ Δ -> Γ ⊆ Δ ▻▻ Ξ
skipⁿ  ε      ι = ι
skipⁿ (Ξ ▻ ν) ι = skip (skipⁿ Ξ ι)

keepⁿ : ∀ {α} {A : Set α} {Γ Δ : Con A} Ξ -> Γ ⊆ Δ -> Γ ▻▻ Ξ ⊆ Δ ▻▻ Ξ
keepⁿ  ε      ι = ι
keepⁿ (Ξ ▻ ν) ι = keep (keepⁿ Ξ ι)

empᵒ : ∀ {α} {A : Set α} {Γ : Con A} -> ε ⊆ Γ
empᵒ {Γ = ε}     = stop
empᵒ {Γ = Γ ▻ σ} = skip empᵒ

-- | The identity embedding.
idᵒ : ∀ {α} {A : Set α} {Γ : Con A} -> Γ ⊆ Γ
idᵒ = stop

-- | The left extension embedding.
extˡ : ∀ {α} {A : Set α} {Γ Δ : Con A} -> Γ ⊆ Δ ▻▻ Γ
extˡ {Γ = ε}     = empᵒ
extˡ {Γ = Γ ▻ σ} = keep extˡ

-- | The right extension embedding.
extʳ : ∀ {α} {A : Set α} {Γ : Con A} Δ -> Γ ⊆ Γ ▻▻ Δ
extʳ Δ = skipⁿ Δ idᵒ

-- | The one element extension embedding.
topᵒ : ∀ {α} {A : Set α} {Γ : Con A} {σ} -> Γ ⊆ Γ ▻ σ
topᵒ = extʳ (ε ▻ _)

mapᶜ-⊆ : ∀ {α β} {A : Set α} {B : Set β} {Γ Δ} {f : A -> B} -> Γ ⊆ Δ -> mapᶜ f Γ ⊆ mapᶜ f Δ
mapᶜ-⊆ {Γ = ε}     ι  ()
mapᶜ-⊆ {Γ = Γ ▻ σ} ι  vz    = mapᵛ (ι vz)
mapᶜ-⊆ {Γ = Γ ▻ σ} ι (vs v) = mapᶜ-⊆ (ι ∘ vs_) v

-- | Rename a variable.
renᵛ : ∀ {α} {A : Set α} {Γ Δ : Con A} {σ} -> Γ ⊆ Δ -> σ ∈ Γ -> σ ∈ Δ
renᵛ ι = ι

shiftᵛⁿ : ∀ {α} {A : Set α} {Γ : Con A} {σ} Δ -> σ ∈ Γ -> σ ∈ Γ ▻▻ Δ
shiftᵛⁿ Δ = renᵛ (extʳ Δ)

shiftᵛ : ∀ {α} {A : Set α} {Γ : Con A} {σ τ} -> σ ∈ Γ -> σ ∈ Γ ▻ τ
shiftᵛ = shiftᵛⁿ (ε ▻ _)

-- We need both first-order and higher-order environments, because the former are more convenient
-- for compilation and the latter are more convenient for evaluation at the type level.

-- | In `Seq P Γ` there a `P σ` for each `σ` from `Γ`.
data Seq {α π} {A : Set α} (P : A -> Set π) : Con A -> Set π where
  ø   : Seq P ε
  _▶_ : ∀ {σ Γ} -> Seq P Γ -> P σ -> Seq P (Γ ▻ σ)

-- We wrap this in `record` in order to get good inference.
-- | In `Env P Γ` there a `P σ` for each `σ` from `Γ`.
record Env {α π} {A : Set α} (P : A -> Set π) (Γ : Con A) : Set (α ⊔ π) where
  constructor PackEnv
  field unpackEnv : ∀ {σ} -> σ ∈ Γ -> P σ
open Env public

foldlˢ
  : ∀ {α π ρ} {A : Set α} {P : A -> Set π} {Γ}
  -> (R : Con A -> Set ρ) -> (∀ {Ξ σ} -> R Ξ -> P σ -> R (Ξ ▻ σ)) -> R ε -> Seq P Γ -> R Γ
foldlˢ R f z  ø      = z
foldlˢ R f z (ρ ▶ α) = f (foldlˢ R f z ρ) α

-- | Apply a natural transformation to each element of a `Seq`.
mapˢ
  : ∀ {α π₁ π₂} {A : Set α} {P₁ : A -> Set π₁} {P₂ : A -> Set π₂} {Γ}
  -> (∀ {σ} -> P₁ σ -> P₂ σ) -> Seq P₁ Γ -> Seq P₂ Γ
mapˢ f = foldlˢ (Seq _) (λ ρ x -> ρ ▶ f x) ø

mapElˢ
  : ∀ {α π₁ π₂} {A : Set α} {P₁ : A -> Set π₁} {P₂ : A -> Set π₂} {Γ}
  -> (∀ {σ} -> σ ∈ Γ -> P₁ σ -> P₂ σ) -> Seq P₁ Γ -> Seq P₂ Γ
mapElˢ f  ø      = ø
mapElˢ f (ρ ▶ α) = mapElˢ (f ∘ vs_) ρ ▶ f vz α

eraseˢ : ∀ {α π} {A : Set α} {P : Set π} {Γ : Con A} -> Seq (λ _ -> P) Γ -> Con P
eraseˢ = foldlˢ _ _▻_ ε

∅ : ∀ {α π} {A : Set α} {P : A -> Set π} -> Env P ε
∅ = PackEnv λ()

_▷_ : ∀ {α π} {A : Set α} {Γ σ} {P : A -> Set π} -> Env P Γ -> P σ -> Env P (Γ ▻ σ)
PackEnv ρ ▷ α = PackEnv λ
  {  vz    -> α
  ; (vs v) -> ρ v
  }

_∘ᵉ_ : ∀ {α π} {A : Set α} {Γ Δ} {P : A -> Set π} -> Env P Δ -> Γ ⊆ Δ -> Env P Γ
PackEnv ρ ∘ᵉ ι = PackEnv (ρ ∘ ι)

withSplitᵉ
  : ∀ {α π ρ} {A : Set α} {Γ σ} {P : A -> Set π} {R : Set ρ}
  -> Env P (Γ ▻ σ) -> (Env P Γ -> P σ -> R) -> R
withSplitᵉ (PackEnv ρ) k = k (PackEnv (ρ ∘ vs_)) (ρ vz)

foldlᵉ
  : ∀ {α π ρ} {A : Set α} {P : A -> Set π} {Γ}
  -> (R : Con A -> Set ρ) -> (∀ {Ξ σ} -> R Ξ -> P σ -> R (Ξ ▻ σ)) -> R ε -> Env P Γ -> R Γ
foldlᵉ {Γ = ε}     R f z ρ = z
foldlᵉ {Γ = Γ ▻ σ} R f z ρ = withSplitᵉ ρ λ ρ′ α -> f (foldlᵉ R f z ρ′) α

-- | Apply a natural transformation to each element of a `Env`.
mapᵉ
  : ∀ {α π₁ π₂} {A : Set α} {P₁ : A -> Set π₁} {P₂ : A -> Set π₂} {Γ}
  -> (∀ {σ} -> P₁ σ -> P₂ σ) -> Env P₁ Γ -> Env P₂ Γ
mapᵉ f = foldlᵉ (Env _) (λ ρ x -> ρ ▷ f x) ∅

mapElᵉ
  : ∀ {α π₁ π₂} {A : Set α} {P₁ : A -> Set π₁} {P₂ : A -> Set π₂} {Γ}
  -> (∀ {σ} -> σ ∈ Γ -> P₁ σ -> P₂ σ) -> Env P₁ Γ -> Env P₂ Γ
mapElᵉ f (PackEnv ρ) = PackEnv λ v -> f v (ρ v)

-- | Look up a variable in an environment.
lookupᵉ : ∀ {α π} {A : Set α} {P : A -> Set π} {Γ σ} -> σ ∈ Γ -> Env P Γ -> P σ
lookupᵉ v (PackEnv ρ) = ρ v

eraseᵉ : ∀ {α π} {A : Set α} {P : Set π} {Γ : Con A} -> Env (λ _ -> P) Γ -> Con P
eraseᵉ = foldlᵉ _ _▻_ ε

record Environment {α β} {A : Set α} (_◆_ : Con A -> A -> Set β) : Set (α ⊔ β) where
  infix 3 _⊢ᵉ_

  field
    varᵈ : ∀ {Γ σ} -> σ ∈ Γ -> Γ ◆ σ
    renᵈ : ∀ {Γ Δ σ} -> Γ ⊆ Δ -> Γ ◆ σ -> Δ ◆ σ

  idᵉ : ∀ {Γ} -> Env (Γ ◆_) Γ
  idᵉ = PackEnv varᵈ

  freshᵉ : ∀ {Γ σ} -> (Γ ▻ σ) ◆ σ
  freshᵉ = varᵈ vz

  _⊢ᵉ_ : Con A -> Con A -> Set (α ⊔ β)
  Ξ ⊢ᵉ Θ = Env (λ σ -> Ξ ◆ σ) Θ

  renᵉ : ∀ {Δ Ξ Γ} -> Δ ⊆ Ξ -> Δ ⊢ᵉ Γ -> Ξ ⊢ᵉ Γ
  renᵉ ι (PackEnv ρ) = PackEnv $ renᵈ ι ∘ ρ

  keepᵉ : ∀ {Δ Γ σ} -> Δ ⊢ᵉ Γ -> Δ ▻ σ ⊢ᵉ Γ ▻ σ
  keepᵉ ρ = renᵉ topᵒ ρ ▷ freshᵉ

  topᵉ : ∀ {Γ σ} -> Γ ◆ σ -> Γ ⊢ᵉ Γ ▻ σ
  topᵉ t = idᵉ ▷ t

  shiftᵉ : ∀ {Δ Γ τ} -> Δ ⊢ᵉ Γ -> Δ ▻ τ ⊢ᵉ Γ
  shiftᵉ = renᵉ topᵒ
