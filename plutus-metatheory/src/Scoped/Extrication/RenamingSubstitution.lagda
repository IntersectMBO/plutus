\begin{code}
module Scoped.Extrication.RenamingSubstitution where
\end{code}

erasure commutes with renaming/substitution

\begin{code}
open import Type
open import Type.BetaNormal
open import Data.Nat
open import Data.Fin
open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality as Eq
open import Algorithmic as A
open import Type.RenamingSubstitution as T
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Completeness
open import Type.BetaNBE.RenamingSubstitution
open import Scoped
open import Scoped.Extrication
open import Algorithmic.RenamingSubstitution as AS
open import Scoped.RenamingSubstitution as SS
open import Builtin

-- type renamings

open import Data.Product renaming (_,_ to _,,_)

backVar : ∀{Γ} → Fin (len⋆ Γ) → Σ Kind λ J → Γ ∋⋆ J
backVar {Γ ,⋆ K} zero    = K ,, Z
backVar {Γ ,⋆ K} (suc i) = let J ,, α = backVar i in J ,, S α

lem-backVar₁ : ∀{Γ J}(α : Γ ∋⋆ J) → proj₁ (backVar (extricateVar⋆ α)) ≡ J
lem-backVar₁ Z = refl
lem-backVar₁ (S α) = lem-backVar₁ α

lem-S : ∀{Φ K J J'} → (p : J ≡ J') → (α : Φ ∋⋆ J)
  → S (Eq.subst (Φ ∋⋆_) p α) ≡ Eq.subst (Φ ,⋆ K ∋⋆_) p (S α)
lem-S refl α = refl

lem-backVar : ∀{Γ J}(α : Γ ∋⋆ J)
  → Eq.subst (Γ ∋⋆_) (lem-backVar₁ α) (proj₂ (backVar (extricateVar⋆ α))) ≡ α
lem-backVar Z = refl
lem-backVar (S α) = trans
  (sym (lem-S (lem-backVar₁ α) (proj₂ (backVar (extricateVar⋆ α)))))
  (cong S (lem-backVar α))

extricateRenNf⋆ : ∀{Γ Δ}(ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J) 
  → Ren⋆ (len⋆ Γ) (len⋆ Δ)
extricateRenNf⋆ ρ⋆ x = extricateVar⋆ (ρ⋆ (proj₂ (backVar x)))

lift⋆-ext : ∀{Γ Δ K}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (α : Fin (len⋆ (Γ ,⋆ K)))
  → lift⋆ (extricateRenNf⋆ ρ⋆) α ≡ extricateRenNf⋆ (T.ext ρ⋆ {K = K}) α -- 
lift⋆-ext ρ⋆ zero = refl
lift⋆-ext ρ⋆ (suc α) = refl

lem-extricateVar⋆ :  ∀{Γ Δ J J'}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (α : Γ ∋⋆ J)
  → (p : J ≡ J')
  → extricateVar⋆ (ρ⋆ α) ≡ extricateVar⋆ (ρ⋆ (Eq.subst (Γ ∋⋆_) p α))
lem-extricateVar⋆ ρ⋆ α refl = refl

ren-extricateNf⋆ :  ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (A : Γ ⊢Nf⋆ J)
  → ren⋆ (extricateRenNf⋆ ρ⋆) (extricateNf⋆ A) ≡ extricateNf⋆ (renNf ρ⋆ A)

ren-extricateNe⋆ :  ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (A : Γ ⊢Ne⋆ J)
  → ren⋆ (extricateRenNf⋆ ρ⋆) (extricateNe⋆ A) ≡ extricateNe⋆ (renNe ρ⋆ A)
ren-extricateNe⋆ ρ⋆ (` x)   = cong
  `
  (trans (lem-extricateVar⋆ ρ⋆ (proj₂ (backVar (extricateVar⋆ x))) (lem-backVar₁ x))
  (cong (extricateVar⋆ ∘ ρ⋆) (lem-backVar x)))
ren-extricateNe⋆ ρ⋆ (A · B) =
  cong₂ _·_ (ren-extricateNe⋆ ρ⋆ A) (ren-extricateNf⋆ ρ⋆ B)

ren-extricateNf⋆ ρ⋆ (Π A)  =
  cong (Π _)
       (trans (ren⋆-cong (lift⋆-ext ρ⋆) (extricateNf⋆ A))
              (ren-extricateNf⋆ (T.ext ρ⋆) A))
ren-extricateNf⋆ ρ⋆ (A ⇒ B)  =
  cong₂ _⇒_ (ren-extricateNf⋆ ρ⋆ A) (ren-extricateNf⋆ ρ⋆ B)
ren-extricateNf⋆ ρ⋆ (ƛ A)  =
  cong (ƛ _)
       (trans (ren⋆-cong (lift⋆-ext ρ⋆) (extricateNf⋆ A)) (ren-extricateNf⋆ (T.ext ρ⋆) A))
ren-extricateNf⋆ ρ⋆ (ne A)   = ren-extricateNe⋆ ρ⋆ A
ren-extricateNf⋆ ρ⋆ (con c)  = refl
ren-extricateNf⋆ ρ⋆ (μ A B)  =
  cong₂ μ (ren-extricateNf⋆ ρ⋆ A) (ren-extricateNf⋆ ρ⋆ B)

extricateSubNf⋆ : ∀{Γ Δ}(σ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ⊢Nf⋆ J) 
  → Sub⋆ (len⋆ Γ) (len⋆ Δ)
extricateSubNf⋆ σ⋆ α = extricateNf⋆ (σ⋆ (proj₂ (backVar α)))

suclem : ∀{Δ K} → (x : Fin (len⋆ Δ)) → Fin.suc x ≡ extricateRenNf⋆ (λ {J} → S {K = K}) x
suclem {Δ ,⋆ _} zero = refl
suclem {Δ ,⋆ _} {K} (suc x) = cong suc (suclem {Δ}{K} x)

slift⋆-exts : ∀{Γ Δ K}
  → (σ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ⊢Nf⋆ J)
  → (α : Fin (len⋆ (Γ ,⋆ K)))
  → slift⋆ (extricateSubNf⋆ σ⋆) α ≡ extricateSubNf⋆ (extsNf σ⋆ {K = K}) α -- 
slift⋆-exts σ⋆ zero = refl
slift⋆-exts {K = K} σ⋆ (suc α) = trans
  (ren⋆-cong (suclem {K = K}) (extricateNf⋆ (σ⋆ (proj₂ (backVar α)))))
  (ren-extricateNf⋆ S (σ⋆ (proj₂ (backVar α))))

{-
sub-extricateNf⋆ :  ∀{Γ Δ J}
  → (σ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ⊢Nf⋆ J)
  → (A : Γ ⊢Nf⋆ J)
  → sub⋆ (extricateSubNf⋆ σ⋆) (extricateNf⋆ A) ≡ extricateNf⋆ (substNf σ⋆ A)

sub-extricateNe⋆ :  ∀{Γ Δ J}
  → (σ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ⊢Nf⋆ J)
  → (A : Γ ⊢NeN⋆ J)
  → sub⋆ (extricateSubNf⋆ σ⋆) (extricateNe⋆ A) ≡ extricateNf⋆ (nf (T.subst (embNf ∘ σ⋆) (embNeN A)))
sub-extricateNe⋆ σ⋆ (` x)   = {!!}
sub-extricateNe⋆ σ⋆ (A · B) = trans (cong₂ _·_ (sub-extricateNe⋆ σ⋆ A) (sub-extricateNf⋆ σ⋆ B)) {!!}
sub-extricateNe⋆ σ⋆ μ1      = refl


sub-extricateNf⋆ σ⋆ (Π {K = K} x A) = cong
  (Π x (extricateK _))
  (trans (trans (sub⋆-cong (slift⋆-exts σ⋆) (extricateNf⋆ A))
                (sub-extricateNf⋆ (extsNf σ⋆) A))
         (cong extricateNf⋆ {x = substNf (extsNf σ⋆) A}{y = reify (eval (T.subst (T.exts (embNf ∘ σ⋆)) (embNf A)) (exte (idEnv _)))}
            (trans (subst-eval (embNf A) idCR (embNf ∘ extsNf σ⋆)) (trans (idext (λ { Z → reflectCR (refl {x = ` Z}) ; (S α) → transCR (transCR (evalCRSubst idCR (ren-embNf S (σ⋆ α))) (ren-eval (embNf (σ⋆ α)) idCR S)) (transCR (symCR (ren-eval (embNf (σ⋆ α)) idCR S)) (idext (λ { Z → reflectCR (refl {x = ` Z}) ; (S β) → symCR (renVal-reflect S (` β))}) (T.weaken (embNf (σ⋆ α)))))}) (embNf A)) (sym (subst-eval (embNf A) (CR,,⋆ (renCR S ∘ idCR) (reflectCR (refl {x = ` Z}))) (T.exts (embNf ∘ σ⋆))))))))
sub-extricateNf⋆ σ⋆ (A ⇒ B) = cong₂ _⇒_ (sub-extricateNf⋆ σ⋆ A) (sub-extricateNf⋆ σ⋆ B)
sub-extricateNf⋆ σ⋆ (ƛ {K = K} x  A) = cong
  (ƛ x (extricateK _))
  (trans (sub⋆-cong (slift⋆-exts σ⋆) (extricateNf⋆ A))
         (trans (sub-extricateNf⋆ (extsNf σ⋆) A)
                (cong extricateNf⋆ {x = substNf (extsNf σ⋆) A}{y = reify (eval (T.subst (T.exts (embNf ∘ σ⋆)) (embNf A)) ((renVal S ∘ idEnv _) ,,⋆ fresh))} (reifyCR (transCR (subst-eval (embNf A) idCR (embNf ∘ extsNf σ⋆)) (transCR (idext (λ { Z → reflectCR {K = K} (refl {x = ` Z}) ; (S α) → transCR (transCR (evalCRSubst idCR (ren-embNf S (σ⋆ α))) (ren-eval (embNf (σ⋆ α)) idCR S)) (transCR (symCR (ren-eval (embNf (σ⋆ α)) idCR S)) (idext (λ { Z → reflectCR (refl {x = ` Z}) ; (S β) → symCR (renVal-reflect S (` β))}) (T.weaken (embNf (σ⋆ α)))) ) }) (embNf A)) (symCR (subst-eval (embNf A) (CR,,⋆ (renCR S ∘ idCR) (reflectCR {K = K} (refl {x = ` Z}))) (T.exts (embNf ∘ σ⋆))))) )))))
sub-extricateNf⋆ σ⋆ (ne A)  = {!!}
sub-extricateNf⋆ σ⋆ (con c) = refl
-}

{-
-- term level renamings

extricateRen : ∀{Φ Ψ Γ Δ}(ρ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J) →
  (ρ : ∀{J}{A : Φ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renNf ρ⋆ A)
  → SS.Ren (len Γ) (len Δ)
extricateRen {Γ = Γ ,⋆ J} {Δ} ρ⋆ ρ (T x) = extricateRen
  (ρ⋆ ∘ S)
  (λ {_}{A} x → Eq.subst (Δ ∋_) (sym (renNf-comp A)) (ρ (T x)))
  x
extricateRen {Γ = Γ , A}  {Δ} ρ⋆ ρ Z     = extricateVar (ρ Z)
extricateRen {Γ = Γ , A}  {Δ} ρ⋆ ρ (S x) = extricateRen ρ⋆ (ρ ∘ S) x
-}



-- these are the two properties of extrication/ren/sub needed to define
-- extricate—→

postulate
  lem[] : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}(N : Γ , A ⊢ B)(W : Γ ⊢ A)
    → extricate N SS.[ extricate W ] ≡ extricate (N AS.[ W ])

  lem[]⋆ : ∀{Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}(N : Γ ,⋆ K ⊢ B)(A : Φ ⊢Nf⋆ K)
    → extricate N SS.[ extricateNf⋆ A ]⋆ ≡ extricate (N AS.[ A ]⋆)
\end{code}
