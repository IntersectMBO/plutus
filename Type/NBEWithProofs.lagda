\begin{code}
module Type.NBEWithProofs where
\end{code} where

## Imports

\begin{code}
open import Type
open import Type.Normal
open import Type.RenamingSubstitution

open import Relation.Binary.HeterogeneousEquality
  renaming (subst to substEq) hiding ([_]) --  using (_≅_; refl; cong; cong₂; trans; sym)
open import Function
open import Data.Product

postulate funext : {A : Set}{B : A → Set}{f : ∀ a → B a}{g : ∀ a → B a} →
                (∀ a → f a ≅ g a) → f ≅ g

postulate funiext : {A : Set}{B : A → Set}{f : ∀{a} → B a}{g : ∀{a} → B a} → 
               (∀ a → f {a} ≅ g {a}) → 
               _≅_ {_}{ {a : A} → B a} f { {a : A} → B a} g

Σeq : {A : Set} {B : A → Set} → {a : A} → {a' : A}(p : a ≅ a') → {b : B a} → {b' : B a'} → substEq B p b ≅ b' → _,_ {B = B} a b ≅ _,_ {B = B} a' b'
Σeq refl refl = refl

fixedtypes : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''} → {p : a ≅ a'} → {q : a'' ≅ a'''} → a' ≅ a'' → p ≅ q
fixedtypes {p = refl} {q = refl} refl = refl
\end{code}


\begin{code}
Ren : Ctx⋆ → Ctx⋆ → Set
Ren Δ Γ = ∀{J} → Δ ∋⋆ J → Γ ∋⋆ J
\end{code}

\begin{code}
mutual
  Val : Ctx⋆ → Kind → Set
  Val Γ * = Γ ⊢Nf⋆ *
  Val Γ (K ⇒ J) = Σ (∀{Δ} → Ren Γ Δ → Val Δ K → Val Δ J) λ f → ∀{Δ Δ'}
    (ρ : Ren Γ Δ)
    (ρ' : Ren Δ Δ')
    (v : Val Δ K)
    → renval J ρ' (f ρ v) ≅ f (ρ' ∘ ρ) (renval K ρ' v)

  renval : ∀{Γ Δ} σ → Ren Γ Δ → Val Γ σ → Val Δ σ
  renval * ρ v = renameNf ρ v
  renval (K ⇒ J) ρ (f , p) = (λ ρ' v → f (ρ' ∘ ρ) v) , λ ρ' ρ'' v → p (ρ' ∘ ρ) ρ'' v

renvalcomp : ∀{Γ Δ E K} → (ρ : Ren Γ Δ) → (ρ' : Ren Δ E) → (v : Val Γ K) → renval K ρ' (renval K ρ v) ≅ renval K (ρ' ∘ ρ) v 
renvalcomp = {!!}
mutual
  reify : ∀{Γ} K → Val Γ K → Γ ⊢Nf⋆ K
  reify * (Π B) = Π B
  reify * (A ⇒ B) = A ⇒ B
  reify * (μ B) = μ B
  reify * (ne A) = ne A
  reify (K ⇒ J) (f , p) = ƛ (reify J (f S (reflect K (` Z)))) 
  
  reflect : ∀{Γ} K → Γ ⊢NeN⋆ K → Val Γ K
  reflect * n = ne n
  reflect (K ⇒ J) f =
    (λ ρ x → reflect J (renameNeN ρ f · (reify K x)))
    , λ ρ ρ' v → trans (rename-reflect J ρ' (renameNeN ρ f · reify K v))
                       (cong₂ (λ x y → reflect J (x · y))
                              (sym (≡-to-≅ (renameNeN-comp ρ ρ' _)))
                              (rename-reify K ρ' v))

  rename-reify : ∀{Γ Δ} K (ρ : Ren Γ Δ)(n : Val Γ K) → renameNf ρ (reify K n) ≅ reify K (renval K ρ n)
  rename-reify * ρ (Π B)   = refl
  rename-reify * ρ (A ⇒ B) = refl
  rename-reify * ρ (μ B)   = refl
  rename-reify * ρ (ne n)  = refl
  rename-reify (K ⇒ J) ρ (f , p) =
    cong ƛ (trans (rename-reify J (ext ρ) (f S (reflect K (` Z))))
                  (cong (reify J) (trans (p S (ext ρ) (reflect K (` Z))) (cong (f (S ∘ ρ)) (rename-reflect K (ext ρ) (` Z))))))

  rename-reflect : ∀{Γ Δ} K (ρ : Ren Γ Δ)(n : Γ ⊢NeN⋆ K) → renval K ρ (reflect K n) ≅ reflect K (renameNeN ρ n)
  rename-reflect * ρ n = refl
  rename-reflect (K ⇒ J) ρ n = Σeq (funiext (λ Γ → funext (λ (ρ' : Ren _ _) → funext (λ v → cong (λ f → reflect J (f · reify K v)) (≡-to-≅ (renameNeN-comp ρ ρ' n)))))) (funiext (λ Δ → funiext (λ Δ → funext (λ ρ' → funext (λ ρ'' → funext (λ v → fixedtypes (trans (cong₂ (λ n₁ v₁ → reflect J (n₁ · v₁)) (≡-to-≅ (renameNeN-comp ρ' ρ'' (renameNeN ρ n))) (sym (rename-reify K ρ'' v))) (sym (rename-reflect J ρ'' (renameNeN ρ' (renameNeN ρ n) · reify K v))))))))))

{-
-- A Partial equivalence relation on values: 'equality on values'
PER : ∀{Γ} K → Val Γ K → Val Γ K → Set
PER *       v v' = reify * v ≅ reify * v'
PER (K ⇒ J) f f' = ∀{Δ}
 → (ρ : Ren _ Δ)
 → {v v' : Val Δ K}
 → PER K v v'
 → PER J (f ρ v) (f' ρ v')  


symPER : ∀{Γ} K {v v' : Val Γ K} → PER K v v' → PER K v' v
symPER *       p = sym p
symPER (K ⇒ J) p = λ ρ q → symPER J (p ρ (symPER K q))

transPER : ∀{Γ} K {v v' v'' : Val Γ K} → PER K v v' → PER K v' v'' → PER K v v''
transPER * p q = trans p q
transPER (K ⇒ J) p q = λ ρ r
  → transPER J (p ρ r) (q ρ (transPER K (symPER K r) r))

reflPER : ∀{Γ} K {v v' : Val Γ K} → PER K v v' → PER K v v
reflPER K p = transPER K p (symPER K p)

mutual
  reifyPER : ∀{Γ} K {v v' : Val Γ K}
    → PER K v v'
    → reify K v ≅ reify K v'
  reifyPER *       p = p
  reifyPER (K ⇒ J) p = cong ƛ (reifyPER J (p S (reflectPER K (refl {x = ` Z})))) 
  
  reflectPER  : ∀{Γ} K {n n' : Γ ⊢NeN⋆ K}
    → n ≅ n'
    → PER K (reflect K n) (reflect K n')
  reflectPER *       p = cong ne p
  reflectPER (K ⇒ J) p =
   λ ρ q → reflectPER J (cong₂ _·_ (cong (renameNeN ρ) p) (reifyPER K q))
-}
\end{code}
  
\begin{code}
Env : Ctx⋆ → Ctx⋆ → Set
Env Δ Γ = ∀{J} → Δ ∋⋆ J → Val Γ J

_,,⋆_ : ∀{Δ Γ} → (σ : Env Γ Δ) → ∀{K}(A : Val Δ K) → Env (Γ ,⋆ K) Δ
(σ ,,⋆ A) Z = A
(σ ,,⋆ A) (S x) = σ x
\end{code}

\begin{code}
mutual
  eval : ∀{Γ Δ K} → Δ ⊢⋆ K → (∀{J} → Δ ∋⋆ J → Val Γ J)  → Val Γ K
  eval (` x)    ρ = ρ x
  eval (Π B)    ρ = Π (eval B ((renval _ S ∘ ρ) ,,⋆ reflect _ (` Z)))
  eval (A ⇒ B) ρ = eval A ρ ⇒ eval B ρ
  eval (ƛ B)    ρ = (λ ρ' v → eval B ((renval _ ρ' ∘ ρ) ,,⋆ v)) ,
    λ ρ' ρ'' v → trans (rename-eval ((renval _ ρ' ∘ ρ) ,,⋆ v) ρ'' B) (cong (λ (γ : Env _ _) → eval B γ) (funiext (λ J → funext (λ { Z → refl ; (S a) → renvalcomp ρ' ρ'' (ρ a)}))))
  eval (A · B) ρ = proj₁ (eval A ρ) id (eval B ρ)
  eval (μ B)    ρ = μ (eval B ((renval _ S ∘ ρ) ,,⋆ reflect _ (` Z)))
  
  rename-eval : ∀{Γ Δ Δ₁ σ} → (γ : Env Γ Δ)(ρ : Ren Δ Δ₁)(t : Γ ⊢⋆ σ) → renval σ ρ (eval t γ) ≅ eval t (renval _ ρ ∘ γ)
  rename-eval γ ρ (` x) = refl
  rename-eval γ ρ (Π t) = cong Π (trans (rename-eval ((renval _ S ∘ γ) ,,⋆ reflect _ (` Z)) (ext ρ) t) (cong (eval t) (funiext (λ a → funext (λ { Z → rename-reflect _ (ext ρ) (` Z) ; (S a₁) → trans (renvalcomp S (ext ρ) (γ a₁)) (sym (renvalcomp ρ S (γ a₁)))}))))) 
  rename-eval γ ρ (A ⇒ B) = cong₂ _⇒_ (rename-eval γ ρ A ) (rename-eval γ ρ B)
  rename-eval γ ρ (ƛ t) = Σeq ? ?
  rename-eval γ ρ (A · B) = {!rename-eval γ ρ A!}
  rename-eval γ ρ (μ t) = cong μ (trans (rename-eval ((renval _ S ∘ γ) ,,⋆ reflect _ (` Z)) (ext ρ) t) (cong (eval t) (funiext (λ a → funext (λ { Z → rename-reflect _ (ext ρ) (` Z) ; (S a₁) → trans (renvalcomp S (ext ρ) (γ a₁)) (sym (renvalcomp ρ S (γ a₁)))}))))) 
  \end{code}

\begin{code}
idEnv : ∀ Γ → Env Γ Γ
idEnv ∅ ()
idEnv (Γ ,⋆ K) Z = reflect K (` Z)
idEnv (Γ ,⋆ K) (S x) = renval _ S (idEnv Γ x)
\end{code}

\begin{code}
nf : ∀{Γ K} → Γ ⊢⋆ K → Γ ⊢Nf⋆ K
nf t = reify _ (eval t (idEnv _))
\end{code}

\begin{code}
_[_]Nf : ∀ {Φ J K}
        → Φ ,⋆ K ⊢Nf⋆ J
        → Φ ⊢Nf⋆ K 
          ------
        → Φ ⊢Nf⋆ J
A [ B ]Nf = nf (embNf A [ embNf B ])
\end{code}

