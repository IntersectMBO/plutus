\begin{code}
module TermIndexedByNormalType.Term.Reduction where
\end{code}

## Imports

\begin{code}
open import Type
open import TermIndexedByNormalType.Term
open import TermIndexedByNormalType.Term.RenamingSubstitution
open import Type.BetaNBE
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
open import Function

\end{code}

## Values

\begin{code}
data Value :  ∀ {J Γ} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-Λ_ : ∀ {Γ K} {B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}
    → {N : Γ ,⋆ K ⊢ B}
      ----------------
    → Value (Λ N)

  V-wrap : ∀{Γ K}
    → {A : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ K}
    → {E : EvalCxt ∥ Γ ∥ K K}
    → {M : Γ ⊢ E [ A [ ne (μ A) ]Nf ]E}
    → {Q : ∥ Γ ∥ ⊢Nf⋆ K}
    → (p : Q ≡ E [ ne (μ A) ]E)
      ----------------
    → Value (wrap A E M p)

\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {J Γ} {A : ∥ Γ ∥ ⊢Nf⋆ J} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′
    
  ξ-·⋆ : ∀ {Γ K}{B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}{L L′ : Γ ⊢ Π B}{A}
    → L —→ L′
      -----------------
    → L ·⋆ A —→ L′ ·⋆ A

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      -------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀ {Γ K}{B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}{N : Γ ,⋆ K ⊢ B}{W}
      -------------------
    → (Λ N) ·⋆ W —→ N [ W ]⋆

  ξ-unwrap : ∀{Γ K}
    → {A : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ K}
    → {E : EvalCxt ∥ Γ ∥ K K}
    → {Q : ∥ Γ ∥ ⊢Nf⋆ K}
    → (p : Q ≡ E [ ne (μ A) ]E)
    → {M M' : Γ ⊢ Q}
    → M —→ M'
    → unwrap E p M —→ unwrap E p M'
{-
  β-wrap : ∀{Γ}
    → {S : ∥ Γ ∥ ,⋆ * ⊢Nf⋆ *}
    → {M : Γ ⊢ S [ μ S ]Nf}    
    → unwrap (wrap {B = S} M) —→ M
-}

  β-wrap : ∀{Γ K}
    → {A : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ K}
    → {E : EvalCxt ∥ Γ ∥ K K}
    → {M : Γ ⊢ E [ A [ ne (μ A) ]Nf ]E}
    → {Q : ∥ Γ ∥ ⊢Nf⋆ K}
    → (p : Q ≡ E [ ne (μ A) ]E)
    → unwrap E p (wrap A E M p) —→ M
\end{code}

\begin{code}
data _—↠_ {J Γ} : {A : ∥ Γ ∥ ⊢Nf⋆ J}{A' : ∥ Γ ∥ ⊢Nf⋆ J} → (Γ ⊢ A) → (Γ ⊢ A') → Set where

  refl—↠ : ∀{A}{M : Γ ⊢ A}
      --------
    → M —↠ M

  trans—↠ : {A : ∥ Γ ∥ ⊢Nf⋆ J}
    {M  M' M'' : Γ ⊢ A}
    → M —→ M'
    → M' —↠ M''
      ---------
    → M —↠ M''
\end{code}

\begin{code}
data Progress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀{N}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M
\end{code}

These are injectivity and disjointness properties that we would get
automatically from unification/pattern matching if we hadn't needed to
introduce Q into wrap and unwarp


\begin{code}
-- if you put a neutral thing into an evaluation context you will get a neutral thing out
lemma-ne : ∀{K J}(N : ∅ ⊢NeN⋆ K)(E : EvalCxt ∅ K J) →
           Σ (∅ ⊢NeN⋆ J) λ N' → E [ ne N ]E ≡ ne N'
lemma-ne N • = N ,, refl
lemma-ne N (E ·E A) with lemma-ne N E
... | (N' ,, p) rewrite p | stabilityNeN N' = (N' · A) ,, trans (readback-neV _) (cong (ne ∘ (N' ·_)) (stability A))

lemma⇒ : ∀{A B : ∅ ⊢Nf⋆ *}{C : ∅ ,⋆ * ⊢Nf⋆ *}{E : EvalCxt ∅ * *} → A ⇒ B ≡ E [ ne (μ C) ]E → ⊥
lemma⇒ {C = C}{E = E} p with lemma-ne (μ C) E
... | (N' ,, q) with trans p q
... | ()

lemmaΠ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{C : ∅ ,⋆ * ⊢Nf⋆ *}{E : EvalCxt ∅ * *} → Π B ≡ E [ ne (μ C) ]E → ⊥
lemmaΠ {C = C}{E = E} p with lemma-ne (μ C) E
... | (N' ,, q) with trans p q
... | ()

lemma·Dom : ∀{J J' K}
  {F  : ∅ ⊢NeN⋆ (J ⇒ K)}
  {F' : ∅ ⊢NeN⋆ (J' ⇒ K)}
  {A  : ∅ ⊢Nf⋆ J}
  {A' : ∅ ⊢Nf⋆ J'} 
  → ne (F _⊢NeN⋆_.· A) ≡ ne (F' · A')
  → J ≡ J'
lemma·Dom refl = refl

lemmaQ' : ∀{J K'}{F F' : ∅ ⊢NeN⋆ (J ⇒ K')}{A A' : ∅ ⊢Nf⋆ J} →
  ne (F _⊢NeN⋆_.· A) ≡ ne (F' · A') → F ≡ F'
lemmaQ' refl = refl

lemmaQ'' : ∀{J K'}{F F' : ∅ ⊢NeN⋆ (J ⇒ K')}{A A' : ∅ ⊢Nf⋆ J} →
  ne (F _⊢NeN⋆_.· A) ≡ ne (F' · A') → A ≡ A'
lemmaQ'' refl = refl

lemmaQ : ∀{K}{Q : ∅ ⊢Nf⋆ K}{S S' : ∅ ,⋆ * ⊢Nf⋆ *}{E E' : EvalCxt ∅ * K}
  → Q ≡ E [ ne (μ S) ]E → Q ≡ E' [ ne (μ S') ]E → S ≡ S'
lemmaQ {Q = .(ne (μ A))} {A} {.A} {•} {•} refl refl = refl
lemmaQ {Q = Q} {A} {A'} {•} {E' ·E x} p q with lemma-ne (μ A') E'
... | (N' ,, r) rewrite r | stabilityNeN N' with trans (sym p) q
... | ()
lemmaQ {Q = Q} {A} {A'} {E ·E x} {•} p q with lemma-ne (μ A) E
... | (N ,, r) rewrite r | stabilityNeN N with trans (sym p) q
... | ()
lemmaQ {Q = Q} {A} {A'} {E ·E B} {E' ·E B'} refl q
  with E [ ne (μ A) ]E
  | inspect (E [_]E) (ne (μ A))
  | lemma-ne (μ A) E
  | E' [ ne (μ A') ]E
  | inspect (E' [_]E) (ne (μ A'))
  | lemma-ne (μ A') E'
lemmaQ {_} {.(readback (eval (embNf (E [ ne (μ A) ]E) · embNf B) (idEnv ∅)))} {A} {A'} {E ·E B} {E' ·E B'} refl q | .(ne N) | Reveal_·_is_.[ eq ] | N ,, refl | .(ne N') | Reveal_·_is_.[ eq' ] | N' ,, refl with lemma·Dom (trans (trans (trans (trans (sym (readback-neV _)) (cong (readback ∘ _·V eval (embNf B) (idEnv _)) (sym (stabilityNeN N)))) q)  (cong (readback ∘ _·V eval (embNf B') (idEnv _))(stabilityNeN N'))) (readback-neV _))
lemmaQ {_} {.(readback (eval (embNf (E [ ne (μ A) ]E) · embNf B) (idEnv ∅)))} {A} {A'} {E ·E B} {E' ·E B'} refl q | .(ne N) | Reveal_·_is_.[ eq ] | N ,, refl | .(ne N') | Reveal_·_is_.[ eq' ] | N' ,, refl | refl = lemmaQ {E = E}{E'} refl (trans (trans eq (cong ne (lemmaQ' (trans (trans (trans (trans (sym (readback-neV _)) (cong (readback ∘ _·V eval (embNf B) (idEnv _)) (sym (stabilityNeN N)))) q)  (cong (readback ∘ _·V eval (embNf B') (idEnv _))(stabilityNeN N'))) (readback-neV _))))) (sym eq'))

lemmaE : ∀{K}{A A' : ∅ ,⋆ * ⊢Nf⋆ *}{E E' : EvalCxt ∅ * K} → E [ ne (μ A) ]E ≡ E' [ ne (μ A') ]E → E ≡ E'
lemmaE {E = •} {•} p = refl
lemmaE {A = A}{A'}{E = •} {E' ·E x₁} p with lemma-ne (μ A') E'
... | (N' ,, r) rewrite r | stabilityNeN N' with p
... | ()
lemmaE {A = A}{A'}{E = E ·E x₁} {•} p with lemma-ne (μ A) E
... | (N ,, r) rewrite r | stabilityNeN N with p
... | ()
lemmaE {A = A}{A'}{E = E ·E B} {E' ·E B'} p
  with E [ ne (μ A) ]E
  | inspect (E [_]E) (ne (μ A))
  | lemma-ne (μ A) E
  | E' [ ne (μ A') ]E
  | inspect (E' [_]E) (ne (μ A'))
  | lemma-ne (μ A') E'
lemmaE {A = A} {A'} {E ·E B} {E' ·E B'} p | .(ne N) | Reveal_·_is_.[ eq ] | N ,, refl | .(ne N') | Reveal_·_is_.[ eq' ] | N' ,, refl with lemma·Dom (trans (trans (sym (trans (cong (readback ∘ _·V eval (embNf B) (idEnv _)) (stabilityNeN N)) (readback-neV _))) p) (trans (cong (readback ∘ _·V eval (embNf B') (idEnv _)) (stabilityNeN N')) (readback-neV _)))
lemmaE {A = A} {A'} {E ·E B} {E' ·E B'} p | .(ne N) | Reveal_·_is_.[ eq ] | N ,, refl | .(ne N') | Reveal_·_is_.[ eq' ] | N' ,, refl | refl = cong₂ _·E_ (lemmaE {E = E}{E'} (trans (trans eq (cong ne (lemmaQ' (trans (trans (sym (trans (cong (readback ∘ _·V eval (embNf B) (idEnv _)) (stabilityNeN N)) (readback-neV _))) p) (trans (cong (readback ∘ _·V eval (embNf B') (idEnv _)) (stabilityNeN N')) (readback-neV _)))))) (sym eq'))) (trans (trans (sym (stability B)) (lemmaQ'' (trans (trans (sym (trans (cong (readback ∘ _·V eval (embNf B) (idEnv _)) (stabilityNeN N)) (readback-neV _))) p) (trans (cong (readback ∘ _·V eval (embNf B') (idEnv _)) (stabilityNeN N')) (readback-neV _))))) (stability B'))
\end{code}


\begin{code}
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ M) = done V-ƛ
progress (M · N) with progress M
progress (M · N) | step p = step (ξ-·₁ p)
progress (.(ƛ _) · N) | done V-ƛ with progress N
progress (.(ƛ _) · N) | done V-ƛ | step p = step (ξ-·₂ V-ƛ p)
progress (.(ƛ _) · N) | done V-ƛ | done VN = step (β-ƛ VN)
progress (.(wrap _ _ _ p) · N) | done (V-wrap {E = E} p) with lemma⇒ {E = E} p
... | ()
progress (Λ M) = done V-Λ_
progress (M ·⋆ A) with progress M
progress (M ·⋆ A) | step p = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (.(wrap _ _ _ p) ·⋆ A) | done (V-wrap {E = E} p) with lemmaΠ {E = E} p
... | ()
progress (wrap A E M p) = done (V-wrap p)
progress (unwrap E p M) with progress M
progress (unwrap E p M) | step q = step (ξ-unwrap p q)
progress (unwrap E p .(ƛ _)) | done V-ƛ with lemma⇒ {E = E} p
... | ()
progress (unwrap E p .(Λ _)) | done V-Λ_ with lemmaΠ {E = E} p
... | ()
progress (unwrap E refl .(wrap _ _ _ q)) | done (V-wrap {E = E'} q) with lemmaQ {E = E'}{E' = E} q refl | lemmaE {E = E'}{E} (trans (sym q) refl)
progress (unwrap E refl .(wrap _ E _ refl)) | done (V-wrap {E = .E} refl) | refl | refl = step (β-wrap refl)
