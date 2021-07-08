\begin{code}
{-# OPTIONS --rewriting #-}

module Algorithmic.Erasure.Reduction where
\end{code}

\begin{code}
open import Function

open import Type
open import Type.BetaNormal
open import Algorithmic as A
import Algorithmic.Reduction as A
import Algorithmic.RenamingSubstitution as A
open import Algorithmic.Erasure
open import Algorithmic.Erasure.RenamingSubstitution
import Untyped.Reduction as U
import Untyped.RenamingSubstitution as U
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Untyped
open import Builtin.Signature Ctx⋆ Kind
  ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Type.BetaNBE.RenamingSubstitution
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List using (List;[];_∷_)
open import Data.Vec hiding (map; [_])
open import Data.Product hiding (map) renaming (_,_ to _,,_)
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
import Utils as Util
open import Relation.Nullary
open import Data.Nat hiding (_<_; _≤?_; _^_; _+_; _≟_; _*_)
open import Data.Integer hiding (suc)
open import Data.Fin using (suc)
import Data.Bool as B
\end{code}

\begin{code}
eraseCtx : ∀{Φ}(Γ : Ctx Φ) → U.Bwd U.Label
eraseCtx ∅        = U.[]
eraseCtx (Γ ,⋆ J) = eraseCtx Γ U.:< U.Type
eraseCtx (Γ , A)  = eraseCtx Γ U.:< U.Term

erase≤C' : ∀{Φ Φ'}{Γ : Ctx Φ}{Γ' : Ctx Φ'} → Γ ≤C' Γ' → eraseCtx Γ U.≤L eraseCtx Γ'
erase≤C' base      = U.base
erase≤C' (skip⋆ p) = U.skipType (erase≤C' p)
erase≤C' (skip p)  = U.skipTerm (erase≤C' p)

-- there could be a simpler version of this without p and q...
erase-arity-lem : ∀ b {Φ}{Γ}(p : proj₁ (ISIG b) ≡ Φ)(q : subst Ctx p (proj₁ (proj₂ (ISIG b))) ≡ Γ) → eraseCtx Γ ≡ U.arity b
erase-arity-lem addInteger refl refl = refl
erase-arity-lem subtractInteger refl refl = refl
erase-arity-lem multiplyInteger refl refl = refl
erase-arity-lem divideInteger refl refl = refl
erase-arity-lem quotientInteger refl refl = refl
erase-arity-lem remainderInteger refl refl = refl
erase-arity-lem modInteger refl refl = refl
erase-arity-lem lessThanInteger refl refl = refl
erase-arity-lem lessThanEqualsInteger refl refl = refl
erase-arity-lem greaterThanInteger refl refl = refl
erase-arity-lem greaterThanEqualsInteger refl refl = refl
erase-arity-lem equalsInteger refl refl = refl
erase-arity-lem concatenate refl refl = refl
erase-arity-lem takeByteString refl refl = refl
erase-arity-lem dropByteString refl refl = refl
erase-arity-lem lessThanByteString refl refl = refl
erase-arity-lem greaterThanByteString refl refl = refl
erase-arity-lem sha2-256 refl refl = refl
erase-arity-lem sha3-256 refl refl = refl
erase-arity-lem verifySignature refl refl = refl
erase-arity-lem equalsByteString refl refl = refl
erase-arity-lem ifThenElse refl refl = refl
erase-arity-lem charToString refl refl = refl
erase-arity-lem append refl refl = refl
erase-arity-lem trace refl refl = refl

eraseITel : ∀ b {Φ}(Δ : Ctx Φ)(σ : SubNf Φ ∅)
          →  A.ITel b Δ σ → U.ITel b (eraseCtx Δ)

eraseFVal : {A B : ∅ ⊢Nf⋆ *}{t : ∅ A.⊢ A ⇒ B}
  → A.Value t → U.FValue (erase t)
eraseFVal (A.V-ƛ t) = U.V-ƛ (erase t)
eraseFVal (A.V-I⇒ b p q r σ p' vs t) =
  U.V-builtin b (erase-arity-lem b p q) (erase≤C' p') (eraseITel b _ σ vs) (erase t)

eraseVal : {A : ∅ ⊢Nf⋆ *}{t : ∅ A.⊢ A}
  → A.Value t → U.Value (erase t)
eraseVal v@(A.V-ƛ t)  = U.V-F (eraseFVal v)
eraseVal (A.V-Λ t)    = U.V-delay
eraseVal (A.V-wrap v) = eraseVal v
eraseVal (A.V-con cn) = U.V-con (eraseTC {∅}{∅} cn)
eraseVal (A.V-IΠ b p q r σ p' vs t) = U.V-builtin⋆ b (erase-arity-lem b p q) (erase≤C' p') (eraseITel b _ σ vs) (erase t)
eraseVal v@(A.V-I⇒ b p q r σ p₁ x t) = U.V-F (eraseFVal v)

eraseITel b ∅        σ vs             = tt
eraseITel b (Δ ,⋆ J) σ (vs ,, A)      = eraseITel b Δ (σ ∘ S) vs
eraseITel b (Δ , A)  σ (vs ,, t ,, v) =
  eraseITel b Δ σ vs  ,, erase t ,, eraseVal v


eraseErr : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : A.Ctx Φ}{e : Γ A.⊢ A}
  → A.Error e → U.Error (erase e)
eraseErr A.E-error = U.E-error
\end{code}

\begin{code}
erase-decIf : ∀{Φ}{Γ : A.Ctx Φ}{A : Φ ⊢Nf⋆ *}{X}(p : Dec X)(t f : Γ A.⊢ A) →
  Util.decIf p (erase t) (erase f) ≡ erase (Util.decIf p t f)
erase-decIf (yes p) t f = refl
erase-decIf (no ¬p) t f = refl
\end{code}

\begin{code}
-- We want that when a builtin eventually computes the untyped and
-- typed semantics would give the same answer. Here we just
-- exhaustively pattern match on the builtin and its typed args to get
-- it to compute.
erase-BUILTIN : ∀ b (σ : SubNf (proj₁ (ISIG b)) ∅)(vs : A.ITel b (proj₁ (proj₂ (ISIG b))) σ) →
  proj₁
  (U.IBUILTIN' b (erase-arity-lem b refl refl) (eraseITel b (proj₁ (proj₂ (ISIG b))) σ vs))
  ≡ erase (proj₁ (A.IBUILTIN b σ vs))
erase-BUILTIN addInteger      σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) = refl
erase-BUILTIN subtractInteger σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) = refl
erase-BUILTIN multiplyInteger σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) = refl
erase-BUILTIN divideInteger σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) with i' ≟ +0
... | yes p = refl
... | no ¬p = refl
erase-BUILTIN quotientInteger σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) with i' ≟ +0
... | yes p = refl
... | no ¬p = refl
erase-BUILTIN remainderInteger σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) with i' ≟ +0
... | yes p = refl
... | no ¬p = refl
erase-BUILTIN modInteger σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) with i' ≟ +0
... | yes p = refl
... | no ¬p = refl
erase-BUILTIN lessThanInteger σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) with i Data.Integer.<? i'
... | yes p = refl
... | no ¬p = refl
erase-BUILTIN lessThanEqualsInteger σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) with i ≤? i'
... | yes p = refl
... | no ¬p = refl
erase-BUILTIN greaterThanInteger σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) with i Util.I>? i'
... | yes p = refl
... | no ¬p = refl
erase-BUILTIN greaterThanEqualsInteger σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) with i Util.I≥? i'
... | yes p = refl
... | no ¬p = refl
erase-BUILTIN equalsInteger σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (integer i')) with i ≟ i'
... | yes p = refl
... | no ¬p = refl
erase-BUILTIN concatenate σ ((tt ,, _ ,, A.V-con (bytestring b)) ,, _ ,, A.V-con (bytestring b')) = refl
erase-BUILTIN takeByteString σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (bytestring b)) = refl
erase-BUILTIN dropByteString σ ((tt ,, _ ,, A.V-con (integer i)) ,, _ ,, A.V-con (bytestring b)) = refl
erase-BUILTIN lessThanByteString σ ((tt ,, _ ,, A.V-con (bytestring b)) ,, _ ,, A.V-con (bytestring b')) = refl
erase-BUILTIN greaterThanByteString σ ((tt ,, _ ,, A.V-con (bytestring b)) ,, _ ,, A.V-con (bytestring b')) = refl
erase-BUILTIN sha2-256 σ (tt ,, _ ,, A.V-con (bytestring b)) = refl
erase-BUILTIN sha3-256 σ (tt ,, _ ,, A.V-con (bytestring b)) = refl
erase-BUILTIN verifySignature σ (((tt ,, _ ,, A.V-con (bytestring b)) ,, _ ,, A.V-con (bytestring b')) ,, _ ,, A.V-con (bytestring b'')) with verifySig b b' b''
... | Util.just _ = refl
... | Util.nothing = refl
erase-BUILTIN equalsByteString σ ((tt ,, _ ,, A.V-con (bytestring b)) ,, _ ,, A.V-con (bytestring b')) = refl
erase-BUILTIN ifThenElse σ ((((tt ,, A) ,, _ ,, A.V-con (bool B.false)) ,, t ,, tv) ,, u ,, uv) = refl
erase-BUILTIN ifThenElse σ ((((tt ,, A) ,, _ ,, A.V-con (bool B.true)) ,, t ,, tv) ,, u ,, uv) = refl
erase-BUILTIN charToString σ (tt ,, _ ,, A.V-con (char c)) = refl
erase-BUILTIN append σ ((tt ,, _ ,, A.V-con (string s)) ,, _ ,, A.V-con (string s')) = refl
erase-BUILTIN trace σ (tt ,, _ ,, A.V-con (string b)) = refl

erase-BUILTIN' : ∀ b {Φ'}{Γ' : Ctx Φ'}(p : proj₁ (ISIG b) ≡ Φ')(q : subst Ctx p (proj₁ (proj₂ (ISIG b))) ≡ Γ')(σ : SubNf Φ' ∅)(vs : A.ITel b Γ' σ){C' : Φ' ⊢Nf⋆ *}(r : subst (_⊢Nf⋆ *) p (proj₂ (proj₂ (ISIG b))) ≡ C') →
  proj₁
  (U.IBUILTIN' b (erase-arity-lem b p q)
   (eraseITel b Γ' σ vs))
  ≡ erase (proj₁ (A.IBUILTIN' b p q σ vs C' r))
erase-BUILTIN' b refl refl σ vs refl = erase-BUILTIN b σ vs

erase—→ : {A : ∅ ⊢Nf⋆ *}{t t' : ∅ A.⊢ A}
  → t A.—→ t' → erase t U.—→ erase t' ⊎ erase t ≡ erase t'
erase—→ (A.ξ-·₁ {M = M} p)                              = map
  U.ξ-·₁
  (cong (_· erase M))
  (erase—→ p)
erase—→ (A.ξ-·₂ {V = V} p q)                            = map
  (U.ξ-·₂ (eraseFVal p))
  ((cong (erase V ·_)))
  (erase—→ q)
erase—→ (A.ξ-·⋆ p)                                      =
  map U.ξ-force (cong force) (erase—→ p)
erase—→ (A.β-ƛ {N = N}{V = V} v)                   =
  inj₁ (subst ((ƛ (erase N) · erase V) U.—→_) (lem[] N V) (U.β-ƛ (eraseVal v)))
erase—→ (A.β-Λ {N = N}{A = A})                          = inj₁ (subst (force (delay (erase N)) U.—→_) (lem[]⋆ N A) U.β-delay)
erase—→ (A.β-wrap p)                                    = inj₂ refl
erase—→ (A.ξ-unwrap p)                                  = erase—→ p
erase—→ (A.ξ-wrap p)                                    = erase—→ p
erase—→ (A.E-·₂ p)                                      =
  inj₁ (U.E-·₂ (eraseFVal p))
erase—→ A.E-·₁                                          = inj₁ U.E-·₁
erase—→ A.E-·⋆                                          = inj₁ U.E-force
erase—→ A.E-unwrap                                      = inj₂ refl
erase—→ A.E-wrap                                        = inj₂ refl
erase—→ (A.β-sbuiltin b σ p q C' r t u vs v) = inj₁ (subst (_ U.—→_) (erase-BUILTIN' b p q σ (vs ,, u ,, v) r)  (U.β-builtin b (erase t) (erase-arity-lem b p q) (eraseITel b _ σ vs) (eraseVal v)))
erase—→ (A.β-sbuiltin⋆ b {A = A} σ p q C' r t vs) = inj₁ (subst (_ U.—→_) (trans (erase-BUILTIN' b p q (subNf-cons σ A) (vs ,, A) r) (lem-erase refl (subNf-cons-[]Nf C') (proj₁ (A.IBUILTIN' b p q (subNf-cons σ A) (vs ,, A) C' r)))) (U.β-builtin⋆ b (erase t) (erase-arity-lem b p q) (eraseITel b _ σ vs)))
\end{code}

-- returning nothing means that the typed step vanishes

\begin{code}
eraseProgress : {A : ∅ ⊢Nf⋆ *}(M : ∅ A.⊢ A)(p : A.Progress M)
  → U.Progress (erase M)
  ⊎ Σ (∅ A.⊢ A) λ N →  (M A.—→ N) × (erase M ≡ erase N)
eraseProgress M (A.step {N = N} p) =
  map U.step (λ q → N ,, p ,, q) (erase—→ p)
eraseProgress M (A.done V)    = inj₁ (U.done (eraseVal V))
eraseProgress M (A.error e)   = inj₁ (U.error (eraseErr e))

erase-progress : ∀{A}(M : ∅ A.⊢ A)
  → U.Progress (erase M)
  ⊎ Σ (∅ A.⊢ A) λ N →  (M A.—→ N) × (erase M ≡ erase N)
erase-progress t = eraseProgress t (A.progress t)
\end{code}
