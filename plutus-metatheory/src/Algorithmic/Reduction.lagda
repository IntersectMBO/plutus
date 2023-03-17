\begin{code}
module Algorithmic.Reduction where
\end{code}

## Imports

\begin{code}
open import Relation.Binary.PropositionalEquality using (_≡_;refl) renaming (subst to substEq)
open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Data.Product using (_×_;∃) renaming (_,_ to _,,_)
open import Data.List as List using (List; _∷_; []; _++_)
open import Data.Bool using (Bool;true;false)
open import Data.Nat using (zero)
open import Data.Unit using (tt)
open import Data.Maybe using (just;from-just)
open import Data.String using (String)

open import Utils using (Kind;*;_⇒_;_∔_≣_;bubble;K) 
open import Type using (Ctx⋆;∅;_,⋆_;Z;_⊢⋆_)
open _⊢⋆_

import Type.RenamingSubstitution as T
open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Type.BetaNBE using (nf)
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;embNf;weakenNf)
open _⊢Nf⋆_
open _⊢Ne⋆_

open import Algorithmic using (Ctx;_⊢_)
open _⊢_
open Ctx
open import Algorithmic.ReductionEC using (Value;BApp;BUILTIN';_—→⋆_;EC;_[_]ᴱ;Error)
                                    using (ruleEC;ruleErr)  -- _—→_ constructors
open EC
open _—→⋆_
open import Algorithmic.ReductionEC.Progress using (step;done;error)

open import Builtin using (Builtin;signature)
open import Builtin.Signature using (Sig;sig;Args;_⊢♯;nat2Ctx⋆;fin2∈⋆;args♯)
open Sig

open Builtin.Signature.FromSig Ctx⋆ (_⊢Nf⋆ *) nat2Ctx⋆ (λ x → ne (` (fin2∈⋆ x))) con _⇒_ Π 
    using (sig2type;♯2*;SigTy;sig2SigTy;sigTy2type;saturatedSigTy;convSigTy)
open SigTy


import Algorithmic.ReductionEC as E
import Algorithmic.ReductionEC.Progress as EP
import Algorithmic.ReductionEC.Determinism as ED
\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→V_

data _—→V_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where

  ξ-·₁ : {A B : ∅ ⊢Nf⋆ *} {L L′ : ∅ ⊢ A ⇒ B} {M : ∅ ⊢ A}
    → L —→V L′
      -----------------
    → L · M —→V L′ · M

  ξ-·₂ : {A B : ∅ ⊢Nf⋆ *}{V : ∅ ⊢ A ⇒ B} {M M′ : ∅ ⊢ A}
    → Value V
    → M —→V M′
      --------------
    → V · M —→V V · M′

  ξ-·⋆ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{L L' : ∅ ⊢ Π B}{A}
    → L —→V L'
      -----------------
    → L ·⋆ A / refl —→V L' ·⋆ A / refl

  β-ƛ : {A B : ∅ ⊢Nf⋆ *}{N : ∅ , A ⊢ B} {V : ∅ ⊢ A}
    → Value V
      -------------------
    → (ƛ N) · V —→V N [ V ]

  β-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{N : ∅ ,⋆ K ⊢ B}{A}
      -------------------
    → (Λ N) ·⋆ A / refl —→V N [ A ]⋆

  β-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : ∅ ⊢ _}
    → Value M
    → unwrap (wrap A B M) refl —→V M

  ξ-unwrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M M' : ∅ ⊢ μ A B}
    → M —→V M'
    → unwrap M refl —→V unwrap M' refl
    
  ξ-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M M' : ∅ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)}
    → M —→V M'
    → wrap A B M —→V wrap A B M'

  β-builtin : ∀{A B}{tn}
      (b : Builtin)
    → (t : ∅ ⊢ A ⇒ B)
    → {pt : tn ∔ 0 ≣ fv♯ (signature b)} 
    → ∀{an} → {pa : an ∔ 1 ≣  args♯ (signature b)}
    → {σB : SigTy pt (bubble pa) B}
    → (bt : BApp b (A B⇒ σB) t) -- one left
    → (u : ∅ ⊢ A)
    → (vu : Value u)
      -----------------------------
    → t · u —→V BUILTIN' b (BApp.step bt vu)
\end{code}

\begin{code}
infix 2 _—→E_

data _—→E_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where
  E-·₂ : ∀{A B : ∅ ⊢Nf⋆ *}{L M}
    → Value L
    → M —→E error A
    → L · M —→E error B
  E-·₁ : ∀{A B : ∅ ⊢Nf⋆ *}{L M}
    → L —→E error (A ⇒ B)
    → L · M —→E error B
  E-·⋆ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{A : ∅ ⊢Nf⋆ K}{L}
    → L —→E error (Π B)
    → L ·⋆ A / refl —→E error _
  E-unwrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : _}
    → M —→E error (μ A B)
    → unwrap M refl —→E error _
  E-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {M : _}
    → M —→E error _
    → wrap A B M —→E error (μ A B) 
  E-top : {A : ∅ ⊢Nf⋆ *} → error A —→E error A
\end{code}


\begin{code}
infix 2 _—→_

data _—→_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where
  red : {A : ∅ ⊢Nf⋆ *}{M  M' : ∅ ⊢ A}
    → M —→V M' → M —→ M'
  err : {A : ∅ ⊢Nf⋆ *}{M : ∅ ⊢ A}
    → M —→E error A → M —→ error A

data _—↠_ : {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → ∅ ⊢ A → Set
  where

  refl—↠ : ∀{A}{M : ∅ ⊢ A}
      --------
    → M —↠ M

  trans—↠ : {A : ∅ ⊢Nf⋆ *}{M  M' M'' : ∅ ⊢ A}
    → M —→ M'
    → M' —↠ M''
      ---------
    → M —↠ M''
\end{code}

\begin{code}
lem—→⋆ : ∀{A}{M M' : ∅ ⊢ A} → M —→⋆ M' → M —→V M'
lem—→⋆ (β-ƛ v) = β-ƛ v
lem—→⋆ (β-Λ refl) = β-Λ
lem—→⋆ (β-wrap v refl) = β-wrap v
lem—→⋆ (β-builtin b t bt u vu) = β-builtin b t bt u vu

lemCS—→V : ∀{A}
         → ∀{B}{L L' : ∅ ⊢ B}
         → (E : EC A B)
         → L —→⋆ L'
         → E [ L ]ᴱ —→V E [ L' ]ᴱ
lemCS—→V [] p = lem—→⋆ p
lemCS—→V (E l· M) p = ξ-·₁ (lemCS—→V E p)
lemCS—→V (V ·r E) p = ξ-·₂ V (lemCS—→V E p)
lemCS—→V (E ·⋆ A / refl) p = ξ-·⋆ (lemCS—→V E p)
lemCS—→V (wrap E) p = ξ-wrap (lemCS—→V E p)
lemCS—→V (unwrap E / refl) p = ξ-unwrap (lemCS—→V E p)

lemCS—→E : ∀{A B}
         → (E : EC A B)
         → E [ error B ]ᴱ —→E error A
lemCS—→E [] = E-top
lemCS—→E (E l· M) = E-·₁ (lemCS—→E E)
lemCS—→E (V ·r E) = E-·₂ V (lemCS—→E E)
lemCS—→E (E ·⋆ A / refl) = E-·⋆ (lemCS—→E E)
lemCS—→E (wrap E) = E-wrap (lemCS—→E E)
lemCS—→E (unwrap E / refl) = E-unwrap (lemCS—→E E)

lemCS—→ : ∀{A}{M M' : ∅ ⊢ A} → M E.—→ M' → M —→ M'
lemCS—→ (ruleEC E p refl refl) = red (lemCS—→V E p)
lemCS—→ (ruleErr E refl) = err (lemCS—→E E)

lemSC—→V : ∀{A}{M M' : ∅ ⊢ A}
  → M —→V M'
  → ∃ λ B 
  → ∃ λ (E : EC A B)
  → ∃ λ L
  → ∃ λ L'
  → (M ≡ E [ L ]ᴱ) × (M' ≡ E [ L' ]ᴱ) × (L —→⋆ L')
lemSC—→V (ξ-·₁ p) with lemSC—→V p
... | B ,, E ,, L ,, L' ,, refl ,, refl ,, q =
  B ,, E l· _ ,, L ,, L' ,, refl ,, refl ,, q
lemSC—→V (ξ-·₂ v p) with lemSC—→V p
... | B ,, E ,, L ,, L' ,, refl ,, refl ,, q =
  B ,, v ·r E ,, L ,, L' ,, refl ,, refl ,, q
lemSC—→V (ξ-·⋆ p) with lemSC—→V p
... | B ,, E ,, L ,, L' ,, refl ,, refl ,, q =
  B ,, E ·⋆ _ / refl ,, L ,, L' ,, refl ,, refl ,, q
lemSC—→V (β-ƛ v) = _ ,, [] ,, _ ,, _ ,, refl ,, refl ,, E.β-ƛ v
lemSC—→V β-Λ = _ ,, [] ,, _ ,, _ ,, refl ,, refl ,, E.β-Λ refl
lemSC—→V (β-wrap v) = _ ,, [] ,, _ ,, _ ,, refl ,, refl ,, E.β-wrap v refl
lemSC—→V (ξ-unwrap p) with lemSC—→V p
... | B ,, E ,, L ,, L' ,, refl ,, refl ,, q =
  B ,, unwrap E / refl ,, L ,, L' ,, refl ,, refl ,, q
lemSC—→V (ξ-wrap p) with lemSC—→V p
... | B ,, E ,, L ,, L' ,, refl ,, refl ,, q =
  B ,, wrap E ,, L ,, L' ,, refl ,, refl ,, q
lemSC—→V (β-builtin b t bt u vu) =
  _ ,, [] ,, _ ,, _ ,, refl ,, refl ,, E.β-builtin b t bt u vu

lemSC—→E : ∀{A}{M : ∅ ⊢ A}
  → M —→E error A
  → ∃ λ B 
  → ∃ λ (E : EC A B)
  → (M ≡ E [ error B ]ᴱ)
lemSC—→E (E-·₂ v p) with lemSC—→E p
... | B ,, E ,, refl = B ,, v ·r E ,, refl
lemSC—→E (E-·₁ p) with lemSC—→E p
... | B ,, E ,, refl = B ,, E l· _ ,, refl
lemSC—→E (E-·⋆ p) with lemSC—→E p
... | B ,, E ,, refl = B ,, E ·⋆ _ / refl ,, refl
lemSC—→E (E-unwrap p) with lemSC—→E p
... | B ,, E ,, refl = B ,, unwrap E / refl ,, refl
lemSC—→E (E-wrap p) with lemSC—→E p
... | B ,, E ,, refl = B ,, wrap E ,, refl
lemSC—→E E-top = _ ,, [] ,, refl

lemSC—→ : ∀{A}{M M' : ∅ ⊢ A} → M —→ M' → M E.—→ M'
lemSC—→ (red p) =
  let B ,, E ,, L ,, L' ,, r ,, r' ,, q = lemSC—→V p in ruleEC E q r r'
lemSC—→ (err p) = let B ,, E ,, p = lemSC—→E p in ruleErr E p 


data Progress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀{N : ∅ ⊢ A}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M

  error :
      Error M
      -------
    → Progress M

progress : {A : ∅ ⊢Nf⋆ *} → (M : ∅ ⊢ A) → Progress M
progress M with EP.progress M
... | step p = step (lemCS—→ p)
... | done v = done v
... | error e = error e

determinism : ∀{A}{L N N' : ∅ ⊢ A} → L —→ N → L —→ N' → N ≡ N'
determinism p q = ED.determinism (lemSC—→ p) (lemSC—→ q)
