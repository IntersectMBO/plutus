```
module Type.BetaNormal.Equality where
```

## Imports

```
open import Function using (id;_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;trans;cong;cong₂)

open import Utils using (*;J)
open import Type using (Ctx⋆;Θ;Φ;Ψ;_∋⋆_)
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;renNf;renNe;renNfTyCon)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Type.RenamingSubstitution using (Ren;ext-cong;ext-id;ext-comp)
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) using (TyCon)
open TyCon
```

```
renNf-cong : {f g : Ren Φ Ψ}
           → (∀ {J}(α : Φ ∋⋆ J) → f α ≡ g α)
           → ∀{K}(A : Φ ⊢Nf⋆ K)
             -------------------------------
           → renNf f A ≡ renNf g A

renNfTyCon-cong : {f g : Ren Φ Ψ}
                → (∀ {J}(α : Φ ∋⋆ J) → f α ≡ g α)
                → (c : TyCon Φ)
                  -------------------------------
                → renNfTyCon f c ≡ renNfTyCon g c
renNfTyCon-cong p integer    = refl
renNfTyCon-cong p bytestring = refl
renNfTyCon-cong p string     = refl
renNfTyCon-cong p unit       = refl
renNfTyCon-cong p bool       = refl
renNfTyCon-cong p (list A)   = cong list (renNf-cong p A) 
renNfTyCon-cong p (pair A B) = cong₂ pair (renNf-cong p A) (renNf-cong p B)
renNfTyCon-cong p pdata       = refl


renNe-cong : {f g : Ren Φ Ψ}
           → (∀ {J}(α : Φ ∋⋆ J) → f α ≡ g α)
           → ∀{K}(A : Φ ⊢Ne⋆ K)
             -------------------------------
           → renNe f A ≡ renNe g A

renNf-cong p (Π A)   = cong Π (renNf-cong (ext-cong p) A)
renNf-cong p (A ⇒ B) = cong₂ _⇒_ (renNf-cong p A) (renNf-cong p B)
renNf-cong p (ƛ A)   = cong ƛ (renNf-cong (ext-cong p) A)
renNf-cong p (ne A)  = cong ne (renNe-cong p A)
renNf-cong p (con c) = cong con (renNfTyCon-cong p c)
renNf-cong p (μ A B) = cong₂ μ (renNf-cong p A) (renNf-cong p B)

renNe-cong p (` α)   = cong ` (p α)
renNe-cong p (A · B) = cong₂ _·_ (renNe-cong p A) (renNf-cong p B)
```

```
renNf-id : (n : Φ ⊢Nf⋆ J)
           --------------
         → renNf id n ≡ n

renNfTyCon-id : (c : TyCon Φ)
           --------------
         → renNfTyCon id c ≡ c
renNfTyCon-id integer    = refl
renNfTyCon-id bytestring = refl
renNfTyCon-id string     = refl
renNfTyCon-id unit       = refl
renNfTyCon-id bool       = refl
renNfTyCon-id (list A)   = cong list (renNf-id A) 
renNfTyCon-id (pair A B) = cong₂ pair (renNf-id A) (renNf-id B)
renNfTyCon-id pdata       = refl

renNe-id : (n : Φ ⊢Ne⋆ J)
           --------------
         → renNe id n ≡ n

renNf-id (Π A)   = cong Π (trans (renNf-cong ext-id A) (renNf-id A))
renNf-id (A ⇒ B) = cong₂ _⇒_ (renNf-id A) (renNf-id B)
renNf-id (ƛ A)   = cong ƛ (trans (renNf-cong ext-id A) (renNf-id A))
renNf-id (ne A)  = cong ne (renNe-id A)
renNf-id (con c) = cong con (renNfTyCon-id c)
renNf-id (μ A B) = cong₂ μ (renNf-id A) (renNf-id B)

renNe-id (` α)   = refl
renNe-id (A · B) = cong₂ _·_ (renNe-id A) (renNf-id B)
```

```
renNf-comp : {g : Ren Φ Ψ}
           → {f : Ren Ψ Θ}
           → ∀{J}(A : Φ ⊢Nf⋆ J)
             -------------------------------------
           → renNf (f ∘ g) A ≡ renNf f (renNf g A)

renNfTyCon-comp : {g : Ren Φ Ψ}
                → {f : Ren Ψ Θ}
                → (c : TyCon Φ)
                  -------------------------------------
                → renNfTyCon (f ∘ g) c ≡ renNfTyCon f (renNfTyCon g c)
renNfTyCon-comp integer    = refl
renNfTyCon-comp bytestring = refl
renNfTyCon-comp string     = refl
renNfTyCon-comp unit       = refl
renNfTyCon-comp bool       = refl
renNfTyCon-comp (list A)   = cong list (renNf-comp A) 
renNfTyCon-comp (pair A B) = cong₂ pair (renNf-comp A) (renNf-comp B)
renNfTyCon-comp pdata       = refl

renNe-comp : {g : Ren Φ Ψ}
           → {f : Ren Ψ Θ}
           → ∀{J}(A : Φ ⊢Ne⋆ J)
             -------------------------------------
           → renNe (f ∘ g) A ≡ renNe f (renNe g A)

renNf-comp (Π B)   = cong Π (trans (renNf-cong ext-comp B) (renNf-comp B))
renNf-comp (A ⇒ B) = cong₂ _⇒_ (renNf-comp A) (renNf-comp B)
renNf-comp (ƛ A)   = cong ƛ (trans (renNf-cong ext-comp A) (renNf-comp A))
renNf-comp (ne A)  = cong ne (renNe-comp A)
renNf-comp (con c) = cong con (renNfTyCon-comp c)
renNf-comp (μ A B) = cong₂ μ (renNf-comp A) (renNf-comp B)

renNe-comp (` x)   = refl
renNe-comp (A · B) = cong₂ _·_ (renNe-comp A) (renNf-comp B)
```
