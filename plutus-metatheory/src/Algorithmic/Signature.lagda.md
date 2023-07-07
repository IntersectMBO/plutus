
```
module Algorithmic.Signature where
```

## Imports

```
open import Data.Nat using (suc)

open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;sym;trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Function using (_∘_)

open import Utils using (*;♯;_∔_≣_)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;Φ)
open _⊢⋆_

open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;renNf;embNf)
open _⊢Nf⋆_
open _⊢Ne⋆_

import Type.RenamingSubstitution as ⋆
open import Type.BetaNBE.Completeness using (reifyCR;idext;exte-lem)
open import Type.BetaNBE.RenamingSubstitution 
                         using (subNf;SubNf;renNf-subNf;subNf-cong;subNf-comp;subNf-cons;extsNf;subNf-lemma;subNf∅;subNf∅≡subNf;subNf∅-subNf;subNf∅-renNf) 
                         renaming (_[_]Nf to _[_])
open import Builtin using (Builtin;signature)
open import Type.BetaNBE using (nf;reify;eval;idEnv;exte)
open import Builtin.Signature using ()
open Builtin.Signature.FromSig _⊢Nf⋆_ _⊢Ne⋆_ ne ` _·_ ^ con _⇒_   Π 
     using (sig2type;SigTy;sigTy2type;convSigTy;sig2typeΠ;sig2type⇒;⊢♯2TyNe♯;mkTy) public
open SigTy
```

```
btype : Builtin → Φ ⊢Nf⋆ *
btype b = subNf∅ (sig2type (signature b))

btype-ren : ∀{Φ Ψ} b (ρ : ⋆.Ren Φ Ψ) → btype b ≡ renNf ρ (btype b)
btype-ren b ρ = sym (subNf∅-renNf ρ (sig2type (signature b)))

btype-sub : ∀{Φ Ψ} b (ρ : SubNf Φ Ψ) → btype b ≡ subNf ρ (btype b)
btype-sub b ρ = sym (subNf∅-subNf ρ (sig2type (signature b)))
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

subSigTy : ∀ {Φ Ψ}
   -- {n⋆ n♯}
  → (σ : SubNf Φ Ψ)
  → ∀{tn tm tt} {pt : tn ∔ tm ≣ tt} 
  → ∀{am an at} {pa : an ∔ am ≣ at} 
  → {A : Φ ⊢Nf⋆ *} → SigTy pt pa A 
  -------------------------
  → SigTy pt pa (subNf σ A)
subSigTy σ (bresult _) = bresult _
subSigTy σ (A B⇒ bt) = (subNf σ A) B⇒ (subSigTy σ bt)
subSigTy σ (sucΠ bt) rewrite (subNf-Π σ (sigTy2type bt)) = sucΠ (subSigTy (extsNf σ) bt) 

_[_]SigTy : ∀{Φ K} 
          → ∀{tn tm tt} {pt : tn ∔ tm ≣ tt} 
          → ∀{am an at} {pa : an ∔ am ≣ at} 
          → {B : Φ ,⋆ K ⊢Nf⋆ *} 
          → SigTy pt pa B 
          → (A : Φ ⊢Nf⋆ K) 
          → SigTy pt pa (B [ A ])
_[_]SigTy bt A  = subSigTy (subNf-cons (ne ∘ `) A) bt

uniqueSigTy :  
      ∀{tn tm tt} → {pt : tn ∔ tm ≣ tt}
    → ∀{an am at} → {pa : an ∔ am ≣ at}
    → ∀{Φ} → {A : Φ ⊢Nf⋆ *}
    → (s s' : SigTy pt pa A)
    → s ≡ s'
uniqueSigTy (bresult _) (bresult _) = refl
uniqueSigTy (A B⇒ s) (.A B⇒ s') = cong (A B⇒_) (uniqueSigTy s s')
uniqueSigTy (sucΠ s) (sucΠ s') = cong sucΠ (uniqueSigTy s s') 
```
 