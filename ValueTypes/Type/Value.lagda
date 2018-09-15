\begin{code}
module Type.Value where
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _⊢V⋆_
\end{code}

## Imports

\begin{code}
open import Function
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)


open import Type
open import Type.RenamingSubstitution
open import Type.Equality
\end{code}

## Type Values

\begin{code}

data Env⋆ (Δ : Ctx⋆) : Ctx⋆ → Set
data _⊢V⋆_ : Ctx⋆ → Kind → Set

data Env⋆ Δ where
  e    : Env⋆ Δ ∅
  _,⋆_ : ∀{Γ} → (σ : Env⋆ Δ Γ) → ∀{K}(A : Δ ⊢V⋆ K) → Env⋆ Δ (Γ ,⋆ K)

data _⊢Ne⋆_ : Ctx⋆ → Kind → Set where
  ` : ∀ {Φ J}
    → Φ ∋⋆ J
      --------
    → Φ ⊢Ne⋆ J

  _·_ : ∀{Φ K J}
    → Φ ⊢Ne⋆ (K ⇒ J)
    → Φ ⊢V⋆ K
      ------
    → Φ ⊢Ne⋆ J


data _⊢V⋆_ where

  Π : ∀ {Φ Ψ K}
    → Ψ ,⋆ K ⊢⋆ *
    → Env⋆ Φ Ψ
      -----------
    → Φ ⊢V⋆ *

  _⇒_ : ∀ {Φ}
    → Φ ⊢V⋆ *
    → Φ ⊢V⋆ *
      ------
    → Φ ⊢V⋆ *

  ƛ :  ∀ {Φ Ψ K J}
    → Ψ ,⋆ K ⊢⋆ J
    → Env⋆ Φ Ψ
      -----------
    → Φ ⊢V⋆ (K ⇒ J)

  μ : ∀{φ Ψ K}
    → Ψ ,⋆ K ⊢⋆ *
    → Env⋆ φ Ψ
      -----------
    → φ ⊢V⋆ *

  ne : ∀{φ K}
    → φ  ⊢Ne⋆ K
      -----------
    → φ ⊢V⋆ K
\end{code}

\begin{code}
lookup⋆ : ∀{Δ Γ} → Env⋆ Δ Γ → ∀ {J} → Γ ∋⋆ J → Δ ⊢V⋆ J
lookup⋆ (σ ,⋆ A) Z = A
lookup⋆ (σ ,⋆ A) (S x) = lookup⋆ σ x
\end{code}

\begin{code}
{-# TERMINATING #-}
eval : ∀{Ψ φ J} → Ψ ⊢⋆ J → Env⋆ φ Ψ → φ ⊢V⋆ J
_·V_ : ∀{φ J K} → φ ⊢V⋆ (J ⇒ K) → φ ⊢V⋆ J → φ ⊢V⋆ K
eval (` x)   vs = lookup⋆ vs x
eval (Π t)   vs = Π t vs
eval (t ⇒ u) vs = eval t vs ⇒ eval u vs
eval (t · u) vs = eval t vs ·V eval u vs
eval (μ t)   vs = μ t vs
eval (ƛ t)   vs = ƛ t vs

ƛ t vs ·V v = eval t (vs ,⋆ v) 
ne n   ·V v = ne (n · v)
\end{code}

\begin{code}
renameNe : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → (∀ {J} → Φ ⊢Ne⋆ J → Ψ ⊢Ne⋆ J)

renameEnv : ∀{Φ Ψ Θ}
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
  (g : Env⋆ Ψ Φ )
  → Env⋆  Θ Φ



renameV : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → (∀ {J} → Φ ⊢V⋆ J → Ψ ⊢V⋆ J)
renameV ρ (Π B vs) = Π B (renameEnv ρ vs)
renameV ρ (A ⇒ B)  = renameV ρ A ⇒ renameV ρ B
renameV ρ (ƛ B vs) = ƛ B (renameEnv ρ vs)
renameV ρ (μ B vs) = μ B (renameEnv ρ vs)
renameV ρ (ne n)   = ne (renameNe ρ n)

renameNe ρ (` x) = ` (ρ x)
renameNe ρ (n · v) = renameNe ρ n · renameV ρ v

renameEnv g e = e
renameEnv g (f ,⋆ A) = (renameEnv g f) ,⋆ (renameV g A)
\end{code}

\begin{code}
weakenV : ∀ {Φ J K}
  → Φ ⊢V⋆ J
    -------------
  → Φ ,⋆ K ⊢V⋆ J
weakenV = renameV S
\end{code}

\begin{code}
weakenEnv : ∀ {Φ K ψ}
  → Env⋆ Φ  ψ
    -------------
  → Env⋆ (Φ ,⋆ K) ψ
weakenEnv = renameEnv S
\end{code}

\begin{code}
extEnv : ∀ {Φ Ψ K} → Env⋆ Φ Ψ
    -----------------------
  → Env⋆ (Φ ,⋆ K) (Ψ ,⋆ K)
extEnv ρ = weakenEnv ρ ,⋆ ne (` Z)
\end{code}

A weak head equality for type values, a bit like values for equations

\begin{code}
--data _E≡_ {Γ} : ∀{Δ} → Env⋆ Γ Δ → Env⋆ Γ Δ → Set

data _V≡_ {Γ} : ∀{J} → Γ ⊢V⋆ J → Γ ⊢V⋆ J → Set
{-
data _Ne≡_ {Γ} : ∀{J} → Γ ⊢Ne⋆ J → Γ ⊢Ne⋆ J → Set where
  `Ne≡ : ∀ {J}
    → {x : Γ ∋⋆ J}
      --------
    → ` x Ne≡ ` x

  ·Ne≡ : ∀{K J}
    → {n n' : Γ ⊢Ne⋆ (K ⇒ J)}
    → n Ne≡ n'
    → {v v' : Γ ⊢V⋆ K}
    → v V≡ v'
    ------
    → (n · v) Ne≡ (n' · v')
-}
data _V≡_ {Γ} where
  ⇒V≡ : {A A' B B' : Γ ⊢V⋆ *}
    -- the others rules are like closures, this one isn't...
    → A V≡ A'
    → B V≡ B'
      --------------------
    → (A ⇒ B) V≡ (A' ⇒ B')
  ΠV≡ : ∀{J Δ}{B B' : Δ ,⋆ J ⊢⋆ *}{vs vs' : Env⋆ Γ Δ}
--    → vs E≡ vs'
--    → B ≡β B'
      ---------------
    → (Π B vs) V≡ (Π B' vs')
  ƛV≡ : ∀{J K Δ}{B B' : Δ ,⋆ J ⊢⋆ K}{vs vs' : Env⋆ Γ Δ}
--    → vs E≡ vs'
--    → B ≡β B'
      ---------------
    → (ƛ B vs) V≡ (ƛ B' vs')
  μV≡ : ∀{J Δ}{B B' : Δ ,⋆ J ⊢⋆ *}{vs vs' : Env⋆ Γ Δ}
--    → vs E≡ vs'
--    → B ≡β B'
      ---------------
    → (μ B vs) V≡ (μ B' vs')
{-
  neV≡ : ∀{K}
    → {A A' : Γ  ⊢Ne⋆ K}
    → A Ne≡ A'
      -----------
    → ne A V≡ ne A'
-}
{-
data _E≡_ {Γ} where
  e≡ : e E≡ e
  ,⋆≡ : ∀{Δ J}{vs vs' : Env⋆ Γ Δ}
    → vs E≡ vs'
    → {v v' : Γ ⊢V⋆ J}
    → v V≡ v'
    → (vs ,⋆ v) E≡ (vs' ,⋆ v)
-}
\end{code}

## Proofs
\begin{code}
{-
renameE≡ : ∀{Φ Ψ Γ}{A B : Env⋆ Φ Γ}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → A E≡ B
    ----------------------------
  → renameEnv ρ A E≡ renameEnv ρ B

renameNe≡ : ∀{Φ Ψ J}{A B : Φ ⊢Ne⋆ J}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → A Ne≡ B
    ----------------------------
  → renameNe ρ A Ne≡ renameNe ρ B


renameV≡ : ∀{Φ Ψ J}{A B : Φ ⊢V⋆ J}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → A V≡ B
    ----------------------------
  → renameV ρ A V≡ renameV ρ B
renameV≡ ρ (⇒V≡ p q) = ⇒V≡ (renameV≡ ρ p) (renameV≡ ρ q)
renameV≡ ρ (ΠV≡ p q) = ΠV≡ (renameE≡ ρ p) q
renameV≡ ρ (ƛV≡ p q) = ƛV≡ (renameE≡ ρ p) q
renameV≡ ρ (μV≡ p q) = μV≡ (renameE≡ ρ p) q
renameV≡ ρ (neV≡ p)  = neV≡ (renameNe≡ ρ p)

renameNe≡ ρ `Ne≡ = `Ne≡
renameNe≡ ρ (·Ne≡ p q) = ·Ne≡ (renameNe≡ ρ p) (renameV≡ ρ q)

renameE≡ ρ e≡ = e≡
renameE≡ ρ (,⋆≡ p q) = ,⋆≡ (renameE≡ ρ p) (renameV≡ ρ q)
-}
\end{code}


\begin{code}
mutual
  renameE-comp : ∀{Δ Φ Ψ Θ}
    (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)(f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J) →
    (vs : Env⋆  Φ Δ) → 
    renameEnv (f ∘ g) vs ≡
    renameEnv f (renameEnv g vs)
  renameE-comp g f e = refl
  renameE-comp g f (vs ,⋆ A) =
    cong₂ (λ x y → x ,⋆ y) (renameE-comp g f vs) (renameV-comp g f A)

  renameV-comp : ∀{Φ Ψ Θ}
    (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)(f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
    → ∀{J}(A : Φ ⊢V⋆ J)
      -------------------------------------------
    → renameV (f ∘ g) A ≡ renameV f (renameV g A)
  renameV-comp g f (Π B vs) = cong (Π B) (renameE-comp g f vs)
  renameV-comp g f (A ⇒ B) =
    cong₂ _⇒_ (renameV-comp g f A) (renameV-comp g f B)
  renameV-comp g f (ƛ B vs) = cong (ƛ B) (renameE-comp g f vs)
  renameV-comp g f (μ B vs) = cong (μ B) (renameE-comp g f vs)
  renameV-comp g f (ne n) = cong ne (renameNe-comp g f n)

  renameNe-comp : ∀{Φ Ψ Θ}
    (g : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)(f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)
    → ∀{J}(A : Φ ⊢Ne⋆ J)
      -------------------------------------------
    → renameNe (f ∘ g) A ≡ renameNe f (renameNe g A)
  renameNe-comp g f (` x) = cong ` refl
  renameNe-comp g f (A · x) = cong₂ _·_ (renameNe-comp g f A) (renameV-comp g f x)
\end{code}

\begin{code}
idEnv : ∀{Γ} → Env⋆ Γ Γ -- ∀{Γ K} → Γ ∋⋆ K → Γ ⊢V⋆ K
idEnv {∅} = e
idEnv {Γ ,⋆ x} = weakenEnv (idEnv {Γ}) ,⋆ (ne (` Z))
\end{code}

\begin{code}
_⟦_⟧ : ∀{ϕ J K} → ϕ ,⋆ K ⊢⋆ J → ϕ ⊢V⋆ K → ϕ ⊢V⋆ J
t ⟦ v ⟧ = eval t (idEnv ,⋆ v )
\end{code}

\begin{code}
{-# TERMINATING #-}
rename-·V : ∀{Γ Δ K J}
  → (A  : Γ ⊢V⋆ K ⇒ J)
  → (B  : Γ ⊢V⋆ K)
  → (ρ : ∀{J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → renameV ρ A ·V renameV ρ B ≡ renameV ρ (A ·V B)

rename-eval : ∀{ϕ Γ Δ J}
  → (B : ϕ ⊢⋆ J)
  → (vs : Env⋆ Γ ϕ)
  → (ρ : ∀{J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → eval B (renameEnv ρ vs) ≡ renameV ρ (eval B vs)
rename-eval (` Z)     (vs ,⋆ A) ρ = refl
rename-eval (` (S x)) (vs ,⋆ A) ρ = rename-eval (` x) vs ρ
rename-eval (Π B)     vs ρ = refl
rename-eval (A ⇒ B)   vs ρ =
  cong₂ _⇒_ (rename-eval A vs ρ) (rename-eval B vs ρ)
rename-eval (ƛ B)      vs ρ = refl
rename-eval (A · B)   vs ρ = trans (cong₂ _·V_ (rename-eval A vs ρ) (rename-eval B vs ρ)) (rename-·V (eval A vs) (eval B vs) ρ)
rename-eval (μ B)     vs ρ = refl

rename-·V (ƛ A vs) B ρ = rename-eval A (vs ,⋆ B) ρ
rename-·V (ne x) B ρ = refl
\end{code}
