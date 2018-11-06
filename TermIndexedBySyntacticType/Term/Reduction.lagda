\begin{code}
module TermIndexedBySyntacticType.Term.Reduction where
\end{code}

## Imports

\begin{code}
open import Type
import Type.RenamingSubstitution as ⋆
open import TermIndexedBySyntacticType.Term
open import TermIndexedBySyntacticType.Term.RenamingSubstitution
open import Type.Equality

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
\end{code}

## Values

\begin{code}
data Value :  ∀ {J Γ} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-Λ_ : ∀ {Γ K} {B : ∥ Γ ∥ ,⋆ K ⊢⋆ *}
    → {N : Γ ,⋆ K ⊢ B}
      ----------------
    → Value (Λ N)

  V-wrap : ∀{Γ K}
    → {S : ∥ Γ ∥ ,⋆ K ⊢⋆ K}
    → {E : EvalCxt ∥ Γ ∥ K K}
    → {M : Γ ⊢ E [ S ⋆.[ μ S ] ]E}
    → {Q : ∥ Γ ∥ ⊢⋆ K}
    → (p : Q ≡ E [ μ S ]E)
      ----------------
    → Value (wrap S E M p)

  V-wrap1 : ∀{Γ K}
   → {pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {arg : ∥ Γ ∥ ⊢⋆ K}
   → {term : Γ ⊢ pat · (μ1 · pat) · arg}
   → Value (wrap1 pat arg term)


  V-con : ∀{Γ}{s : ∥ Γ ∥ ⊢⋆ #}{tcn : TyCon}
    → (cn : TermCon (con tcn s))
    → Value (con {Γ} cn)
\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {J Γ} {A : ∥ Γ ∥ ⊢⋆ J} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′

  ξ-·⋆ : ∀ {Γ B}{L L′ : Γ ⊢ Π B}{A}
    → L —→ L′
      -----------------
    → L ·⋆ A —→ L′ ·⋆ A
    
  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      -------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀ {Γ}{B : ∥ Γ ∥ ,⋆ * ⊢⋆ *}{N : Γ ,⋆ * ⊢ B}{W}
      -------------------
    → (Λ N) ·⋆ W —→ N [ W ]⋆

  ξ-unwrap : ∀{Γ K}
    → {S : ∥ Γ ∥ ,⋆ K ⊢⋆ K}
    → {E : EvalCxt ∥ Γ ∥ K K}
    → {Q : ∥ Γ ∥ ⊢⋆ K}
    → (p : Q ≡ E [ μ S ]E)
    → {M M' : Γ ⊢ Q}
    → M —→ M'
    → unwrap E p M —→ unwrap E p M'

  β-wrap : ∀{Γ K}
    → {S : ∥ Γ ∥ ,⋆ K ⊢⋆ K}
    → {E : EvalCxt ∥ Γ ∥ K K}
    → {M : Γ ⊢ E [ S ⋆.[ μ S ] ]E}
    → {Q : ∥ Γ ∥ ⊢⋆ K}
    → (p : Q ≡ E [ μ S ]E)
    → unwrap E p (wrap S E M p) —→ M

  β-wrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢⋆ K}
    → {term : Γ ⊢ pat · (μ1 · pat) · arg}
    → unwrap1 (wrap1 pat arg term) —→ term

  ξ-unwrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢⋆ K}
    → {M M' : Γ ⊢ μ1 · pat · arg}
    → M —→ M'
    → unwrap1 M —→ unwrap1 M'


  -- this is a temporary hack as currently the type eq relation only has
  -- reflexivity in it.
  ξ-conv₁ : ∀{Γ J}{A : ∥ Γ ∥ ⊢⋆ J}{L : Γ ⊢ A}
    → conv (refl≡β A) L —→ L

  ξ-conv₂ : ∀{Γ J}{A B : ∥ Γ ∥ ⊢⋆ J}{L L' : Γ ⊢ A}{p : A ≡β B}
    → L —→ L'
    → conv p L —→ conv p L'
\end{code}


\begin{code}
data Progress {A : ∅ ⊢⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀ {N}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M
  unhandled : Progress M 
\end{code}

These are injectivity and disjointness properties that we would get
automatically from unification/pattern matching if we hadn't needed to
introduce Q into wrap and unwarp

\begin{code}
disjoint-μ⇒ : ∀{A B : ∅ ⊢⋆ *}{C : ∅ ,⋆ * ⊢⋆ *}{E : EvalCxt ∅ * *} → A ⇒ B ≡ E [ μ C ]E → ⊥
disjoint-μ⇒ {E = •}      ()
disjoint-μ⇒ {E = E ·E A} ()

disjoint-μΠ : ∀{K}{B : ∅ ,⋆ K ⊢⋆ *}{C : ∅ ,⋆ * ⊢⋆ *}{E : EvalCxt ∅ * *} → Π B ≡ E [ μ C ]E → ⊥
disjoint-μΠ {E = •}      ()
disjoint-μΠ {E = E ·E A} ()

lemma·Fun : ∀{J K'}{F F' : ∅ ⊢⋆ (J ⇒ K')}{A A' : ∅ ⊢⋆ J} →
  F _⊢⋆_.· A ≡ F' · A' → F ≡ F'
lemma·Fun refl = refl

lemma·Dom : ∀{J J' K}
  {F  : ∅ ⊢⋆ (J ⇒ K)}
  {F' : ∅ ⊢⋆ (J' ⇒ K)}
  {A  : ∅ ⊢⋆ J}
  {A' : ∅ ⊢⋆ J'} 
  → F _⊢⋆_.· A ≡ F' · A'
  → J ≡ J'
lemma·Dom refl = refl

disjoint-μμ1 : ∀{K K'}{C : ∅ ,⋆ * ⊢⋆ *}
  {E : EvalCxt ∅ _ K'}{E' : EvalCxt ∅ _ _} →
  E [ μ1 {K = K} ]E ≡ E' [ μ C ]E → ⊥
disjoint-μμ1 {E = •} {E' ·E x} ()
disjoint-μμ1 {E = E ·E x} {•} ()
disjoint-μμ1 {E = E ·E x} {E' ·E x₁} p with lemma·Dom p
... | refl = disjoint-μμ1 (lemma·Fun p)

disjoint-μμ1' : ∀{K}{C : ∅ ,⋆ * ⊢⋆ *}{pat : ∅ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
 {arg : ∅ ⊢⋆ K}{E : EvalCxt ∅ _ _} → μ1 · pat · arg  ≡ E [ μ C ]E → ⊥
disjoint-μμ1' p = disjoint-μμ1 p

disjoint-μcon : ∀{tcn : TyCon}{s : ∅ ⊢⋆ #}{C : ∅ ,⋆ * ⊢⋆ *}{E : EvalCxt ∅ * *} → con tcn s ≡ E [ μ C ]E → ⊥
disjoint-μcon {E = •}      ()
disjoint-μcon {E = E ·E x} ()

lemmaQ'' : ∀{J K'}{F F' : ∅ ⊢⋆ (J ⇒ K')}{A A' : ∅ ⊢⋆ J} →
  F _⊢⋆_.· A ≡ F' · A' → A ≡ A'
lemmaQ'' refl = refl

lemmaQ : ∀{K}{Q : ∅ ⊢⋆ K}{S S' : ∅ ,⋆ * ⊢⋆ *}{E E' : EvalCxt ∅ * K}
  → Q ≡ E [ μ S ]E → Q ≡ E' [ μ S' ]E → S ≡ S'
lemmaQ {E = •} {•} refl refl = refl
lemmaQ {E = •} {E' ·E x} refl ()
lemmaQ {E = E ·E x} {•} refl ()
lemmaQ {E = E ·E x} {E' ·E x₁} refl q with lemma·Dom q
lemmaQ {E = E ·E _} {E' ·E _} refl q | refl = lemmaQ refl (lemma·Fun q)

-- there are several things wrong here, Q and A' are not used
lemmaE : ∀{K}{Q : ∅ ⊢⋆ K}{A A' : ∅ ,⋆ * ⊢⋆ *}{E E' : EvalCxt ∅ * K}
  → E [ μ A ]E ≡ E' [ μ A ]E → E ≡ E'
lemmaE {E = •} {•} p = refl
lemmaE {E = •} {E' ·E x₁} ()
lemmaE {E = E ·E x₁} {•} ()
lemmaE {E = E ·E x₁} {E' ·E x₂} x with lemma·Dom x
lemmaE {A = A}{A' = A'} {E ·E x₁} {E' ·E x₂} x | refl =
  cong₂ _·E_ (lemmaE {Q = E [ μ A ]E}{A' = A'}{E = E}{E'} (lemma·Fun x)) (lemmaQ'' x)
\end{code}

\begin{code}
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ M)    = done V-ƛ
progress (L · M)  with progress L
...                   | unhandled = unhandled
...                   | step p  = step (ξ-·₁ p)
progress (.(ƛ _) · M) | done V-ƛ with progress M
progress (.(ƛ _) · M) | done V-ƛ | step p = step (ξ-·₂ V-ƛ p)
progress (.(ƛ _) · M) | done V-ƛ | done VM = step (β-ƛ VM)
progress (.(ƛ _) · M) | done V-ƛ | unhandled = unhandled
progress (.(wrap _ _ _ p) · M) | done (V-wrap p) with disjoint-μ⇒ p
... | ()
progress (Λ M)    = done V-Λ_
progress (M ·⋆ A) with progress M
progress (M ·⋆ A) | step p = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (.(wrap _ _ _ p) ·⋆ A) | done (V-wrap p) with disjoint-μΠ p
... | ()
progress (M ·⋆ A) | unhandled = unhandled
progress (wrap A E M p) = done (V-wrap p)
progress (unwrap E p M) with progress M
progress (unwrap E p M) | step q = step (ξ-unwrap p q)
progress (unwrap E p .(ƛ _)) | done V-ƛ with disjoint-μ⇒ p
... | ()
progress (unwrap E p .(Λ _)) | done V-Λ_ with disjoint-μΠ p
... | ()
progress (unwrap E p .(con cn)) | done (V-con cn) with disjoint-μcon p
... | ()
progress (unwrap E p .(wrap _ _ _ q)) | done (V-wrap {M = M} q) with lemmaQ q p
progress (unwrap E refl .(wrap _ E' M q)) | done (V-wrap {S = A}{E = E'} {M} q) | refl with lemmaE {Q = E [ μ A ]E}{A' = A} q
progress (unwrap E refl .(wrap _ E M refl)) | done (V-wrap {S = _} {.E} {M} refl) | refl | refl = step (β-wrap refl)
progress (unwrap E p M) | done V-wrap1 with disjoint-μμ1 p
progress (unwrap E p .(wrap1 _ _ _)) | done V-wrap1 | ()
progress (unwrap E p M) | unhandled = unhandled
progress (wrap1 _ _ t) = done V-wrap1
progress (unwrap1 t) with progress t
progress (unwrap1 t) | step p = step (ξ-unwrap1 p)
progress (unwrap1 .(wrap _ _ _ p)) | done (V-wrap p) with disjoint-μμ1 p
progress (unwrap1 .(wrap _ _ _ p)) | done (V-wrap p) | ()
progress (unwrap1 .(wrap1 _ _ _)) | done V-wrap1 = step β-wrap1
progress (unwrap1 t) | unhandled = unhandled
progress (conv p t) = unhandled
progress (con cn)   = done (V-con cn)
progress (builtin bn σ X) = unhandled
\end{code}
