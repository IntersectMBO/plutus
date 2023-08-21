```
module Type.BetaNormal.Equality where
```

## Imports

```
open import Data.Vec using (Vec;[];_∷_) 
open import Data.List using (List;[];_∷_)
open import Function using (id;_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;trans;cong;cong₂)

open import Utils using (*;J)
open import Type using (Ctx⋆;Θ;Φ;Ψ;_∋⋆_)
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;renNf;renNe;renNf-List;renNf-VecList)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Type.RenamingSubstitution using (Ren;ext-cong;ext-id;ext-comp)
```

```
renNf-cong : {f g : Ren Φ Ψ}
           → (∀ {J}(α : Φ ∋⋆ J) → f α ≡ g α)
           → ∀{K}(A : Φ ⊢Nf⋆ K)
             -------------------------------
           → renNf f A ≡ renNf g A
renNe-cong : {f g : Ren Φ Ψ}
           → (∀ {J}(α : Φ ∋⋆ J) → f α ≡ g α)
           → ∀{K}(A : Φ ⊢Ne⋆ K)
             -------------------------------
           → renNe f A ≡ renNe g A
renNf-cong-List : ∀ {f g : Ren Φ Ψ}
              (p : ∀ {J} (α : Φ ∋⋆ J) → f α ≡ g α)
              (xs : List (Φ ⊢Nf⋆ *))
              -----------------------------------------
            → renNf-List f xs ≡ renNf-List g xs         
renNf-cong-VecList : ∀ {f g : Ren Φ Ψ}
              (p : ∀ {J} (α : Φ ∋⋆ J) → f α ≡ g α){n}
              (xss : Vec (List (Φ ⊢Nf⋆ *)) n)
              -----------------------------------------
            → renNf-VecList f xss ≡ renNf-VecList g xss           
renNf-cong p (Π A)     = cong Π (renNf-cong (ext-cong p) A)
renNf-cong p (A ⇒ B)   = cong₂ _⇒_ (renNf-cong p A) (renNf-cong p B)
renNf-cong p (ƛ A)     = cong ƛ (renNf-cong (ext-cong p) A)
renNf-cong p (ne A)    = cong ne (renNe-cong p A)
renNf-cong p (con c)   = cong con (renNf-cong p c)
renNf-cong p (μ A B)   = cong₂ μ (renNf-cong p A) (renNf-cong p B)
renNf-cong p (SOP xss) = cong SOP (renNf-cong-VecList p xss)

renNe-cong p (` α)   = cong ` (p α)
renNe-cong p (A · B) = cong₂ _·_ (renNe-cong p A) (renNf-cong p B)
renNe-cong p (^ x)   = refl

renNf-cong-List p [] = refl
renNf-cong-List p (x ∷ xs) = cong₂ _∷_ (renNf-cong p x) (renNf-cong-List p xs)
renNf-cong-VecList p [] = refl
renNf-cong-VecList p (xs ∷ xss) = cong₂ _∷_ (renNf-cong-List p xs) (renNf-cong-VecList p xss)
```

```
renNf-id : (n : Φ ⊢Nf⋆ J)
           --------------
         → renNf id n ≡ n
renNe-id : (n : Φ ⊢Ne⋆ J)
           --------------
         → renNe id n ≡ n
renNe-id-List : 
           (n : List (Φ ⊢Nf⋆ J))
           ------------------------------
         → renNf-List id n ≡ n 
renNe-id-VecList : ∀{m}
           (n : Vec (List (Φ ⊢Nf⋆ J)) m)
           ------------------------------
         → renNf-VecList id n ≡ n         

renNf-id (Π A)     = cong Π (trans (renNf-cong ext-id A) (renNf-id A))
renNf-id (A ⇒ B)   = cong₂ _⇒_ (renNf-id A) (renNf-id B)
renNf-id (ƛ A)     = cong ƛ (trans (renNf-cong ext-id A) (renNf-id A))
renNf-id (ne A)    = cong ne (renNe-id A)
renNf-id (con c)   = cong con (renNf-id c)
renNf-id (μ A B)   = cong₂ μ (renNf-id A) (renNf-id B)
renNf-id (SOP xss) = cong SOP (renNe-id-VecList xss)

renNe-id (` α)   = refl
renNe-id (A · B) = cong₂ _·_ (renNe-id A) (renNf-id B)
renNe-id (^ x)   = refl

renNe-id-List [] = refl
renNe-id-List (x ∷ xs) = cong₂ _∷_ (renNf-id x) (renNe-id-List xs)
renNe-id-VecList [] = refl
renNe-id-VecList (xs ∷ xss) = cong₂ _∷_ (renNe-id-List xs) (renNe-id-VecList xss)
```

```
renNf-comp : {g : Ren Φ Ψ}
           → {f : Ren Ψ Θ}
           → ∀{J}(A : Φ ⊢Nf⋆ J)
             -------------------------------------
           → renNf (f ∘ g) A ≡ renNf f (renNf g A)
renNe-comp : {g : Ren Φ Ψ}
           → {f : Ren Ψ Θ}
           → ∀{J}(A : Φ ⊢Ne⋆ J)
             -------------------------------------
           → renNe (f ∘ g) A ≡ renNe f (renNe g A)
renNf-comp-List :
            {g : Ren Φ Ψ} 
          → {f : Ren Ψ Θ}
          → (xs : List (Φ ⊢Nf⋆ *))
            ----------------------------------------------------------------
          → renNf-List (f ∘ g) xs ≡ renNf-List f (renNf-List g xs)           
renNf-comp-VecList : ∀{n}
            {g : Ren Φ Ψ} 
          → {f : Ren Ψ Θ}
          → (xss : Vec (List (Φ ⊢Nf⋆ *)) n) 
            ----------------------------------------------------------------
          → renNf-VecList (f ∘ g) xss ≡ renNf-VecList f (renNf-VecList g xss)


renNf-comp (Π B)     = cong Π (trans (renNf-cong ext-comp B) (renNf-comp B))
renNf-comp (A ⇒ B)   = cong₂ _⇒_ (renNf-comp A) (renNf-comp B)
renNf-comp (ƛ A)     = cong ƛ (trans (renNf-cong ext-comp A) (renNf-comp A))
renNf-comp (ne A)    = cong ne (renNe-comp A)
renNf-comp (con c)   = cong con (renNf-comp c)
renNf-comp (μ A B)   = cong₂ μ (renNf-comp A) (renNf-comp B)
renNf-comp (SOP xss) = cong SOP (renNf-comp-VecList xss)

renNe-comp (` x)   = refl
renNe-comp (A · B) = cong₂ _·_ (renNe-comp A) (renNf-comp B)
renNe-comp (^ x)   = refl

renNf-comp-List [] = refl
renNf-comp-List (x ∷ xs) = cong₂ _∷_ (renNf-comp x) (renNf-comp-List xs)
renNf-comp-VecList [] = refl
renNf-comp-VecList (xs ∷ xss) = cong₂ _∷_ (renNf-comp-List xs) (renNf-comp-VecList xss)

```
 