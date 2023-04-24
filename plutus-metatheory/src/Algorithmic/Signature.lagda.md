
```
module Algorithmic.Signature where
```

## Imports

```
open import Data.Nat using (suc)

open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;sym;trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Function using (_∘_)

open import Utils using (*;_∔_≣_)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;Φ)
open _⊢⋆_

open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;renNf;embNf)
open _⊢Nf⋆_
open _⊢Ne⋆_

import Type.RenamingSubstitution as ⋆
open import Type.BetaNBE.Completeness using (reifyCR;idext;exte-lem)
open import Type.BetaNBE.RenamingSubstitution 
                         using (subNf;SubNf;renNf-subNf;subNf-cong;subNf-comp;subNf-cons;extsNf;subNf-lemma) 
                         renaming (_[_]Nf to _[_])
open import Type.BetaNBE.Stability using (stability)
open import Builtin using (Builtin;signature)
open import Builtin.Signature using (Sig;sig;nat2Ctx⋆;fin2∈⋆)
open import Type.BetaNBE using (nf;reify;eval;idEnv;exte)
open Builtin.Signature.FromSig Ctx⋆ (_⊢Nf⋆ *) nat2Ctx⋆ (λ x → ne (` (fin2∈⋆ x))) con _⇒_ Π 
     using (sig2type;SigTy;sigTy2type;convSigTy) public
open SigTy


```

```
btype' : Builtin → Φ ⊢Nf⋆ *
btype' b = subNf (λ()) (sig2type (signature b))

btype-∅ : ∀ {A : ∅ ⊢Nf⋆ *} → A ≡ subNf {∅} {∅} (λ()) {*} A
btype-∅ {A} = begin
             A
            ≡⟨ sym (stability A) ⟩
             nf (embNf A)
           ≡⟨ cong nf (sym (⋆.sub-∅ (embNf A)  (embNf ∘  λ()))) ⟩
             nf (⋆.sub (embNf ∘ λ()) (embNf A))
           ≡⟨ refl ⟩
             subNf (λ ()) A
           ∎

-- A version of btype' where btype {∅} b = sig2type (signature b) holds definitionally
btype : Builtin → Φ ⊢Nf⋆ *
btype {∅} b = sig2type (signature b)
btype {Φ ,⋆ x} b = btype' b

-- Both versions are the same
btype-btype' : ∀ {Φ} b → btype {Φ} b ≡ btype' {Φ} b
btype-btype' {∅} b = btype-∅
btype-btype' {Φ ,⋆ x} b = refl

btype'-ren : ∀{Φ Ψ} b (ρ : ⋆.Ren Φ Ψ) → btype' b ≡ renNf ρ (btype' b)
btype'-ren b ρ = begin
             btype' b
             ≡⟨ refl ⟩
             subNf (λ()) (sig2type (signature b))
             ≡⟨ subNf-cong {f = λ()} {renNf ρ ∘ λ ()} (λ ()) (sig2type (signature b)) ⟩
             subNf (renNf ρ ∘ λ ()) (sig2type (signature b))
             ≡⟨ renNf-subNf (λ()) ρ (sig2type (signature b)) ⟩
             renNf ρ (btype' b)
           ∎

btype-ren : ∀{Φ Ψ} b (ρ : ⋆.Ren Φ Ψ) → btype b ≡ renNf ρ (btype b)
btype-ren b ρ = trans (btype-btype' b) (trans (btype'-ren b ρ) (cong (renNf ρ) (sym (btype-btype' b))))

btype'-sub : ∀{Φ Ψ} b (ρ : SubNf Φ Ψ) → btype' b ≡ subNf ρ (btype' b)
btype'-sub b ρ = begin 
           btype' b
          ≡⟨ refl ⟩
           subNf (λ()) (sig2type (signature b))
          ≡⟨ subNf-cong {f = λ()} {subNf ρ ∘ λ ()} (λ ()) (sig2type (signature b)) ⟩
            subNf (subNf ρ ∘ (λ ())) (sig2type (signature b))
          ≡⟨ subNf-comp (λ()) ρ (sig2type (signature b)) ⟩
           subNf ρ (subNf (λ()) (sig2type (signature b)))
          ≡⟨ refl ⟩
           subNf ρ (btype' b)
          ∎

btype-sub : ∀{Φ Ψ} b (ρ : SubNf Φ Ψ) → btype b ≡ subNf ρ (btype b)
btype-sub b ρ = trans ((btype-btype' b)) (trans (btype'-sub b ρ) (cong (subNf ρ) (sym (btype-btype' b))))
```

## Substitution in Signature types

```
subNf-Π : ∀{Φ Ψ J}(ρ : SubNf Φ Ψ)(B : Φ ,⋆ J ⊢Nf⋆ *) →  subNf ρ (Π B) ≡ Π (subNf (extsNf ρ) B)
subNf-Π {Φ}{Ψ}{J} ρ B = begin
    subNf ρ (Π B)
  ≡⟨ refl ⟩
    Π (reify (eval (⋆.sub (⋆.exts (embNf ∘ ρ)) (embNf B)) (exte (idEnv _))))
  ≡⟨ cong nf (cong Π (subNf-lemma ρ (embNf B)) ) ⟩
    Π (reify (eval (⋆.sub (embNf ∘ extsNf ρ) (embNf B)) (exte (idEnv _))))
  ≡⟨ cong Π (reifyCR (idext exte-lem ((⋆.sub (embNf ∘ extsNf ρ) (embNf B))))) ⟩
   Π (reify (eval (⋆.sub (embNf ∘ extsNf ρ) (embNf B)) (idEnv _)))
  ≡⟨ refl ⟩   -- nf def
    Π (nf (⋆.sub (embNf ∘ extsNf ρ) (embNf B)))
  ≡⟨ refl ⟩
    Π (subNf (extsNf ρ) B)
  ∎

subSigTy : ∀ {n m}
  → (σ : SubNf (nat2Ctx⋆ n) (nat2Ctx⋆ m))
  → ∀{tn tm tt} {pt : tn ∔ tm ≣ tt} 
  → ∀{am an at} {pa : an ∔ am ≣ at} 
  → {A : nat2Ctx⋆ n ⊢Nf⋆ *} → SigTy pt pa A 
  -------------------------
  → SigTy pt pa (subNf σ A)
subSigTy σ (bresult _) = bresult _
subSigTy σ (A B⇒ bt) = (subNf σ A) B⇒ (subSigTy σ bt)
subSigTy σ (sucΠ bt) rewrite (subNf-Π σ (sigTy2type bt))
            = sucΠ (subSigTy (extsNf σ) bt)

_[_]SigTy : ∀{n} 
          → ∀{tn tm tt} {pt : tn ∔ tm ≣ tt} 
          → ∀{am an at} {pa : an ∔ am ≣ at} 
          → {B : (nat2Ctx⋆ (suc n)) ⊢Nf⋆ *} 
          → SigTy pt pa B 
          → (A : (nat2Ctx⋆ n) ⊢Nf⋆ *) 
          → SigTy pt pa (B [ A ])
_[_]SigTy bt A  = subSigTy (subNf-cons (ne ∘ `) A) bt

uniqueSigTy :          
      ∀{tn tm tt} → {pt : tn ∔ tm ≣ tt}
    → ∀{an am at} → {pa : an ∔ am ≣ at}
    → ∀{n}{A : (nat2Ctx⋆ n) ⊢Nf⋆ *}
    → (s s' : SigTy pt pa A)
    → s ≡ s'
uniqueSigTy (bresult _) (bresult _) = refl
uniqueSigTy (A B⇒ s) (.A B⇒ s') = cong (A B⇒_) (uniqueSigTy s s')
uniqueSigTy (sucΠ s) (sucΠ s') = cong sucΠ (uniqueSigTy s s') 
```
