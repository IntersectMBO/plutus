\begin{code}
module Type.BetaNBE.Completeness where
\end{code}

\begin{code}
open import Type
open import Type.Equality
open import Type.RenamingSubstitution
open import Type.BetaNormal
open import Type.BetaNBE

open import Relation.Binary.PropositionalEquality hiding (subst)
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Function
\end{code}

\begin{code}
-- A Partial equivalence relation on values: 'equality' for values
-- It's also a Kripke Logical Relation
PER : ∀{Γ} K → Val Γ K → Val Γ K → Set
PER #       n        n'        = n ≡ n'
PER *       n        n'        = n ≡ n'
PER (K ⇒ J) (inj₁ n) (inj₁ n') = reify (inj₁ n) ≡ reify (inj₁ n')
PER (K ⇒ J) (inj₂ f) (inj₁ n') = ⊥
PER (K ⇒ J) (inj₁ n) (inj₂ f)  = ⊥
PER (K ⇒ J) (inj₂ f) (inj₂ f') =
  Unif (inj₂ f)
  ×
  Unif (inj₂ f')
  ×
  ∀ {Δ}
     → (ρ : Ren _ Δ)
     → {v v' : Val Δ K}
     → PER K v v'
       ---------------------------------------------------------
     → PER J (renval ρ (inj₂ f) ·V v) (renval ρ (inj₂ f') ·V v')
  where
    -- Uniformity
    Unif : ∀{Γ K J} → Val Γ (K ⇒ J) → Set
    Unif {Γ}{K}{J} f = ∀{Δ Δ'}
      → (ρ : Ren Γ Δ)
      → (ρ' : Ren Δ Δ')
      → (v v' : Val Δ K)
      → PER K v v'
        ------------------------------------------------------------------------
      → PER J  (renval ρ' (renval ρ f ·V v)) (renval (ρ' ∘ ρ) f ·V renval ρ' v')
\end{code}

PER is symmetric and transitive, it is not reflexive, but we if we
have a value that is related to something else by PER then we can
derive a reflexivity result for it.

\begin{code}
symPER : ∀{Γ} K {v v' : Val Γ K}
  → PER K v v'
    ----------
  → PER K v' v
symPER #                          p = sym p
symPER *                          p = sym p
symPER (K ⇒ J) {inj₁ n} {inj₁ n'} p = sym p
symPER (K ⇒ J) {inj₁ n} {inj₂ f'} ()
symPER (K ⇒ J) {inj₂ f} {inj₁ n'} ()
symPER (K ⇒ J) {inj₂ f} {inj₂ f'} (p , p' , p'') =
  p' , p , λ ρ q → symPER J (p'' ρ (symPER K q))

transPER : ∀{Γ} K {v v' v'' : Val Γ K}
  → PER K v v'
  → PER K v' v''
    ------------
  → PER K v v''
transPER #                                  p q = trans p q
transPER *                                     p q = trans p q
transPER (K ⇒ J) {inj₁ n} {inj₁ n'} {inj₁ n''} p q = trans p q
transPER (K ⇒ J) {inj₁ n} {inj₁ n'} {inj₂ f''} p ()
transPER (K ⇒ J) {inj₁ n} {inj₂ f'} () q
transPER (K ⇒ J) {inj₂ f} {inj₁ n'} () q
transPER (K ⇒ J) {inj₂ f} {inj₂ f'} {inj₁ n} p ()
transPER (K ⇒ J) {inj₂ f} {inj₂ f'} {inj₂ f''} (p , p' , p'') (q , q' , q'') =
  p , q' , λ ρ r → transPER J (p'' ρ r) (q'' ρ (transPER K (symPER K r) r))

reflPER : ∀{Γ} K {v v' : Val Γ K}
  → PER K v v'
    ---------
  → PER K v v
reflPER K p = transPER K p (symPER K p)
\end{code}

reify takes two related values and produces to identical normal
forms. reflectPER works in the other direction for neutral terms. They
are not mutually defined in this version of NBE.

Composing reify with the fundamental theorem of PER defined later and
using reflectPER to build identify environments will give us the
completeness result.

\begin{code}
reflectPER : ∀{Γ} K → {n n' : Γ ⊢NeN⋆ K}
  → n ≡ n' → PER K (reflect n) (reflect n')
reflectPER #    p = cong ne p
reflectPER *       p = cong ne p
reflectPER (K ⇒ J) p = cong ne p

reifyPER : ∀{Γ} K → {v v' : Val Γ K}
  → PER K v v' → reify v ≡ reify v'
reifyPER #                       p = p
reifyPER *                          p = p
reifyPER (K ⇒ J) {inj₁ n} {inj₁ n'} p = p
reifyPER (K ⇒ J) {inj₁ n} {inj₂ f'} ()
reifyPER (K ⇒ J) {inj₂ f} {inj₁ n'} ()
reifyPER (K ⇒ J) {inj₂ f} {inj₂ f'} (p , p' , p'') =
  cong ƛ (reifyPER J (p'' S (reflectPER K refl)))
\end{code}

'equality' for environements

\begin{code}
PEREnv : ∀ {Γ Δ} → (η η' : Env Γ Δ) →  Set
PEREnv {Γ}{Δ} η η' = ∀{K} (x : Γ ∋⋆ K) → PER K (η x) (η' x) 
\end{code}

Closure under environment extension

\begin{code}
PER,,⋆ : ∀{Γ Δ K}{η η' : Env Γ Δ}
  → PEREnv η η'
  → {v v' : Val Δ K}
  → PER K v v'
    ----------------------------
  → PEREnv (η ,,⋆ v) (η' ,,⋆ v')
PER,,⋆ p q Z = q
PER,,⋆ p q (S x) = p x
\end{code}

Closure under application

\begin{code}
PERApp : ∀{Γ K J}
  → {f f' : Val Γ (K ⇒ J)}
  → PER (K ⇒ J) f f'
  → {v v' : Val Γ K}
  → PER K v v'
  → PER J (f ·V v) (f' ·V v')
PERApp {f = inj₁ n} {inj₁ .n} refl q = reflectPER _ (cong (n ·_) (reifyPER _ q))
PERApp {f = inj₁ n} {inj₂ f'} () q
PERApp {f = inj₂ f} {inj₁ n} () q
PERApp {f = inj₂ f} {inj₂ f'} (p , p' , p'') q = p'' id q
\end{code}

renval commutes with reflect

\begin{code}
renval-reflect : ∀{Γ Δ K}(ρ : Ren Γ Δ)(n : Γ ⊢NeN⋆ K) → PER K (renval ρ (reflect n)) (reflect (renameNeN ρ n))
renval-reflect {K = #}  ρ n = refl
renval-reflect {K = *}     ρ n = refl
renval-reflect {K = K ⇒ J} ρ n = refl 
\end{code}

renaming commutes with reify

\begin{code}
rename-reify : ∀{K Γ Δ}{v v' : Val Γ K} → PER K v v' → (ρ : Ren Γ Δ) → renameNf ρ (reify v) ≡ reify (renval ρ v')
rename-reify {#}                         refl           ρ = refl
rename-reify {*}                            refl           ρ = refl
rename-reify {K ⇒ J} {v = inj₁ n} {inj₁ .n} refl           ρ = refl
rename-reify {K ⇒ J} {v = inj₁ n} {inj₂ f'} ()             ρ
rename-reify {K ⇒ J} {v = inj₂ f} {inj₁ n'} ()             ρ
rename-reify {K ⇒ J} {v = inj₂ f} {inj₂ f'} (p , p' , p'') ρ = cong ƛ (trans (rename-reify (p'' S (reflectPER K (refl {x = ` Z}))) (ext ρ)) (reifyPER J (transPER J ( p' S (ext ρ) _ _ (reflectPER K refl) ) (PERApp {f = renval (S ∘ ρ) (inj₂ f')}{renval (S ∘ ρ) (inj₂ f')} ((λ ρ₁ ρ' v → p' (ρ₁ ∘ S ∘ ρ) ρ' v) , (λ ρ₁ ρ' v → p' (ρ₁ ∘ S ∘ ρ) ρ' v) , λ ρ' q → (proj₂ (proj₂ (reflPER (K ⇒ J) (symPER (K ⇒ J) (p , p' , p'')))) (ρ' ∘ S ∘ ρ) q)) (renval-reflect (ext ρ) (` Z))))))
\end{code}

first functor law for renval

\begin{code}
renval-id : ∀ {K Γ}{v v' : Val Γ K} →
  PER K v v' → 
  PER K (renval id v) v'
renval-id {#}                         refl = renameNf-id _
renval-id {*}                            refl = renameNf-id _
renval-id {K ⇒ J} {v = inj₁ n} {inj₁ n'} refl = cong ne (renameNeN-id _)
renval-id {K ⇒ J} {v = inj₁ n} {inj₂ f'} ()
renval-id {K ⇒ J} {v = inj₂ f} {inj₁ n'} () 
renval-id {K ⇒ J} {v = inj₂ f} {inj₂ f'} p    = p
\end{code}

second functor law for renval

\begin{code}
renval-comp : ∀ {K Γ Δ Θ}(ρ : Ren Γ Δ)(ρ' : Ren Δ Θ){v v' : Val Γ K} →
  PER K v v' → 
  PER K (renval (ρ' ∘ ρ) v) (renval ρ' (renval ρ v'))
renval-comp {#}   ρ ρ'                    refl           =
  renameNf-comp ρ ρ' _
renval-comp {*}      ρ ρ'                    refl           =
  renameNf-comp ρ ρ' _
renval-comp {K ⇒ K₁} ρ ρ' {inj₁ n} {inj₁ n'} refl           =
  cong ne (renameNeN-comp ρ ρ' _)
renval-comp {K ⇒ K₁} ρ ρ' {inj₁ x} {inj₂ y} ()
renval-comp {K ⇒ K₁} ρ ρ' {inj₂ y} {inj₁ x} ()
renval-comp {K ⇒ K₁} ρ ρ' {inj₂ y} {inj₂ y₁} (p , p' , p'') =
  (λ ρ'' ρ''' v → p (ρ'' ∘ ρ' ∘ ρ) ρ''' v)
  ,
  (λ ρ'' ρ''' v → p' (ρ'' ∘ ρ' ∘ ρ) ρ''' v)
  ,
  λ ρ'' q → p'' (ρ'' ∘ ρ' ∘ ρ) q
\end{code}

PER is closed under renaming

\begin{code}
renPER : ∀{Γ Δ K}{v v' : Val Γ K}
  → (ρ : Ren Γ Δ)
  → PER K v v'
  → PER K (renval ρ v) (renval ρ v')
renPER {K = #}                      ρ p              = cong (renameNf ρ) p
renPER {K = *}                         ρ p              = cong (renameNf ρ) p
renPER {K = K ⇒ K₁} {inj₁ n} {inj₁ .n} ρ refl           = refl
renPER {K = K ⇒ K₁} {inj₁ n} {inj₂ f'} ρ ()
renPER {K = K ⇒ K₁} {inj₂ f} {inj₁ n'} ρ ()
renPER {K = K ⇒ K₁} {inj₂ f} {inj₂ f'} ρ (p , p' , p'') =
  (λ ρ' ρ'' v → p (ρ' ∘ ρ) ρ'' v)
  ,
  (λ ρ' ρ'' v → p' (ρ' ∘ ρ) ρ'' v)
  ,
  λ ρ' q → p'' (ρ' ∘ ρ) q
\end{code}

PER is closed under application
\begin{code}
renval·V : ∀{K J Γ Δ}
  → (ρ : Ren Γ Δ)
  → {f f' : Val Γ (K ⇒ J)}
  → PER (K ⇒ J) f f'
  → {v v' : Val Γ K}
  → PER K v v'
    ------------------------------------------------------
  → PER J (renval ρ (f ·V v)) (renval ρ f' ·V renval ρ v')
renval·V {J = #} ρ {inj₁ n} {inj₁ .n} refl {v}{v'} q =
  cong (ne ∘ (renameNeN ρ n ·_))
       (trans ( rename-reify (reflPER _ q) ρ ) (reifyPER _ (renPER ρ q)))
renval·V {J = *} ρ {inj₁ n} {inj₁ .n} refl {v}{v'} q =
  cong (ne ∘ (renameNeN ρ n ·_))
       (trans ( rename-reify (reflPER _ q) ρ ) (reifyPER _ (renPER ρ q)))
renval·V {J = J ⇒ K} ρ {inj₁ n} {inj₁ .n} refl {v}{v'} q =
  cong (ne ∘ (renameNeN ρ n ·_))
       (trans ( rename-reify (reflPER _ q) ρ ) (reifyPER _ (renPER ρ q)))
renval·V ρ {inj₁ n} {inj₂ f} () q
renval·V ρ {inj₂ f} {inj₁ n'} () q
renval·V ρ {inj₂ f} {inj₂ f'} (p , p' , p'') q =
  transPER _ (p id ρ _ _ q) (p'' ρ (renPER ρ (reflPER _ (symPER _ q))))
\end{code}

identity extension lemma, renaming commutes with eval, defined mutually

\begin{code}
idext : ∀{Γ Δ K}{η η' : Env Γ Δ}
  → PEREnv η η'
  → (t : Γ ⊢⋆ K)
    ----------------------------
  → PER K (eval t η) (eval t η')

renval-eval : ∀{Γ Δ Θ K}
  → (t : Δ ⊢⋆ K)
  → {η η' : ∀{J} → Δ ∋⋆ J → Val Γ J}
  → (p : PEREnv η η')
  → (ρ : Ren Γ Θ )
    ----------------------------------------------------
  → PER K (renval ρ (eval t η)) (eval t (renval ρ ∘ η'))
renval-eval (` x) p ρ = renPER ρ (p x)
renval-eval (Π B) p ρ = cong Π (trans (renval-eval B (PER,,⋆ (renPER S ∘ p) (reflectPER _ (refl {x = ` Z}))) (ext ρ)) (idext (λ{ Z → renval-reflect (ext ρ) (` Z) ; (S x) → transPER _ (symPER _ (renval-comp S (ext ρ) (reflPER _ (symPER _ (p x))))) (renval-comp ρ S (reflPER _ (symPER _ (p x))))}) B))
renval-eval (A ⇒ B) p ρ = cong₂ _⇒_ (renval-eval A p ρ) (renval-eval B p ρ)
renval-eval (ƛ B) {η}{η'} p ρ =
  (λ ρ' ρ'' v v' q → transPER _ (renval-eval B (PER,,⋆ (renPER (ρ' ∘ ρ) ∘ p) q) ρ'') (idext (λ { Z → renPER ρ'' (reflPER _ (symPER _ q)) ; (S x) → symPER _ (renval-comp (ρ' ∘ ρ) ρ'' (p x))}) B))
  ,
  (λ ρ' ρ'' v v' q → transPER _ (renval-eval B (PER,,⋆ (renPER ρ' ∘ renPER ρ ∘ reflPER _ ∘ symPER _ ∘ p) q) ρ'') (idext (λ { Z → renPER ρ'' (reflPER _ (symPER _ q)) ; (S x) → symPER _ (renval-comp ρ' ρ'' (renPER ρ (reflPER _ (symPER _ (p x)))))}) B))
  ,
  λ ρ' q → idext (λ { Z → q ; (S x) → renval-comp ρ ρ' (p x) }) B
renval-eval (A · B) p ρ = transPER _ (renval·V ρ (idext (reflPER _ ∘ p) A) (idext (reflPER _ ∘ p) B)) (PERApp (renval-eval A p ρ) (renval-eval B p ρ))
renval-eval (μ B) p ρ = transPER _ (renval-reflect ρ _) (reflectPER _ (cong μ (trans (rename-reify (idext (PER,,⋆ (renPER S ∘ reflPER _ ∘ p) (reflectPER _ refl)) B) (ext ρ)) (reifyPER _ (transPER _ (renval-eval B (PER,,⋆ (renPER S ∘ p) (reflectPER _ refl)) (ext ρ)) (idext (λ { Z → renval-reflect (ext ρ) (` Z) ; (S x) → transPER _ (symPER _ (renval-comp S (ext ρ) (p x))) (renval-comp ρ S (p x)) }) B))))))
renval-eval (size⋆ n)   p ρ = refl
renval-eval (con tcn s) p ρ = cong (con tcn) (renval-eval s p ρ)

idext p (` x)   = p x
idext p (Π B)   = cong Π (idext (PER,,⋆ (renPER S ∘ p) (reflectPER _ refl)) B)
idext p (A ⇒ B) = cong₂ _⇒_ (idext p A) (idext p B)
idext p (ƛ B)   =
  (λ ρ ρ' v v' q → transPER _ (renval-eval B (PER,,⋆ (renPER ρ ∘ reflPER _ ∘ p) q) ρ')
                     (idext (λ { Z → renPER ρ' (reflPER _ (symPER _ q)) ; (S x) → symPER _ (renval-comp ρ ρ' (reflPER _ (p x)))}) B))
  ,
  (λ ρ ρ' v v' q → transPER _ (renval-eval B (PER,,⋆ (renPER ρ ∘ reflPER _ ∘ symPER _ ∘ p) q) ρ')
     (idext (λ { Z → renPER ρ' (reflPER _ (symPER _ q)) ; (S x) → symPER _ (renval-comp ρ ρ' (reflPER _ (symPER _ (p x))))}) B))
  ,
  λ ρ q → idext (PER,,⋆ (renPER ρ ∘ p) q) B
idext p (A · B) = PERApp (idext p A) (idext p B)
idext p (μ  B)  =
  reflectPER _
          (cong μ (reifyPER _ (idext (PER,,⋆ (renPER S ∘ p) (reflectPER _ refl)) B)))
idext p (size⋆ n)   = refl
idext p (con tcn s) = cong (con tcn) (idext p s)
\end{code}

(pre) renaming commutes with eval

\begin{code}
rename-eval : ∀{Γ Δ Θ K}
  (t : Θ ⊢⋆ K)
  {η η' : ∀{J} → Δ ∋⋆ J → Val Γ J}
  (p : PEREnv η η')
  (ρ : Ren Θ Δ) →
  PER K (eval (rename ρ t) η) (eval t (η' ∘ ρ))
rename-eval (` x) p ρ = p (ρ x)
rename-eval (Π B) p ρ =
  cong Π (trans (rename-eval
                  B
                  (PER,,⋆ (renPER S ∘ p)
                          (reflectPER _ (refl {x = ` Z}))) (ext ρ))
       (idext (λ{ Z     → reflectPER _ refl
                ; (S x) → (renPER S ∘ reflPER _ ∘ symPER _ ∘ p) (ρ x)}) B))
rename-eval (A ⇒ B) p ρ = cong₂ _⇒_ (rename-eval A p ρ) (rename-eval B p ρ) 
rename-eval (ƛ B) p ρ =
  (λ ρ' ρ'' v v' q → transPER _
                       (renval-eval (rename (ext ρ) B)
                        (PER,,⋆ (renPER ρ' ∘ reflPER _ ∘ p) q) ρ'')
                       (idext (λ { Z → renPER ρ'' (reflPER _ (symPER _ q))
                                 ; (S x) → symPER _ (renval-comp ρ' ρ'' (reflPER _ (p x)))}) (rename (ext ρ) B)))
  ,
  (λ ρ' ρ'' v v' q → transPER _ (renval-eval B (PER,,⋆ (renPER ρ' ∘ reflPER _ ∘ symPER _ ∘ p ∘ ρ) q) ρ'')
                                (idext (λ { Z →  renPER ρ'' (reflPER _ (symPER _ q))
                                          ; (S x) → symPER _ (renval-comp ρ' ρ'' (reflPER _ (symPER _ (p (ρ x)))))}) B))
  ,
  λ ρ' q → transPER _ (rename-eval B (PER,,⋆ (renPER ρ' ∘ p) q) (ext ρ))
                      (idext (λ { Z → reflPER _ (symPER _ q) ; (S x) → renPER ρ' (reflPER _ (symPER _ (p (ρ x)))) }) B)
rename-eval (A · B) p ρ = PERApp (rename-eval A p ρ) (rename-eval B p ρ)
rename-eval (μ B) p ρ = reflectPER _ (cong μ (reifyPER _ (transPER _ (rename-eval B (PER,,⋆ (renPER S ∘ p) (reflectPER _ refl)) (ext ρ)) (idext (λ { Z → reflectPER _ refl ; (S x) → renPER S ((reflPER _ ∘ symPER _ ∘ p) (ρ x))}) B))))
rename-eval (size⋆ n)   p ρ = refl
rename-eval (con tcn s) p ρ = cong (con tcn) (rename-eval s p ρ)
\end{code}

Subsitution lemma

\begin{code}
subst-eval : ∀{Γ Δ Θ K}
  (t : Θ ⊢⋆ K)
  {η η' : ∀{J} → Δ ∋⋆ J → Val Γ J}
  (p : PEREnv η η')
  (σ : Sub Θ Δ) →
  PER K (eval (subst σ t) η) (eval t (λ x → eval (σ x) η'))
subst-eval (` x) p σ = idext p (σ x)
subst-eval (Π B) p σ = cong Π (trans (subst-eval B (PER,,⋆ (renPER S ∘ p) (reflectPER _ (refl {x = ` Z}))) (exts σ)) (idext (λ{ Z → reflectPER _ (refl {x = ` Z}) ; (S x) → transPER _ (rename-eval (σ x) (PER,,⋆ (renPER S ∘ reflPER _ ∘ symPER _ ∘ p) (reflectPER _ (refl {x = ` Z}))) S) (symPER _ (renval-eval (σ x)  (reflPER _ ∘ symPER _ ∘ p) S)) }) B))
subst-eval (A ⇒ B) p σ = cong₂ _⇒_ (subst-eval A p σ) (subst-eval B p σ)
subst-eval (ƛ B) p σ =
  (λ ρ ρ' v v' q → transPER _
                     (renval-eval (subst (exts σ) B)
                      (PER,,⋆ (renPER ρ ∘ reflPER _ ∘ p) q) ρ')
                     (idext (λ { Z    → renPER ρ' (reflPER _ (symPER _ q))
                               ; (S x) → symPER _ (renval-comp ρ ρ' (reflPER _ (p x)))})
                            (subst (exts σ) B)))
  ,
  (λ ρ ρ' v v' q → transPER _ (renval-eval B (PER,,⋆ (renPER ρ ∘ idext (reflPER _ ∘ symPER _ ∘ p) ∘ σ) q) ρ')
     (idext (λ { Z → renPER ρ' (reflPER _ (symPER _ q))
               ; (S x) → symPER _ (renval-comp ρ ρ' (idext (reflPER _ ∘ symPER _ ∘ p) (σ x)))}) B))
  ,
  λ ρ q → transPER _ (subst-eval B (PER,,⋆ (renPER ρ ∘ p) q) (exts σ))
    (idext (λ { Z → reflPER _ (symPER _ q)
              ; (S x) → transPER _
                          (rename-eval (σ x)
                           (PER,,⋆ (renPER ρ ∘ reflPER _ ∘ symPER _ ∘ p)
                            (reflPER _ (symPER _ q)))
                           S)
                          (symPER _ (renval-eval (σ x) (reflPER _ ∘ symPER _ ∘ p) ρ))})
           B)
subst-eval (A · B) p σ = PERApp (subst-eval A p σ) (subst-eval B p σ)
subst-eval (μ B) p σ = reflectPER _ (cong μ (reifyPER _ (transPER _ (subst-eval B (PER,,⋆ (renPER S ∘ p) (reflectPER _ refl)) (exts σ)) (idext (λ { Z → reflectPER _ refl ; (S x) → transPER _ (rename-eval (σ x) (PER,,⋆ (renPER S ∘ reflPER _ ∘ symPER _ ∘ p) (reflectPER _ refl)) S) (symPER _ (renval-eval (σ x) (reflPER _ ∘ symPER _ ∘ p) S))}) B))))
subst-eval (size⋆ n)   p ρ = refl
subst-eval (con tcn s) p ρ = cong (con tcn) (subst-eval s p ρ)
\end{code}

Fundamental Theorem of logical relations for PER

\begin{code}
fund : ∀{Γ Δ K}{η η' : Env Γ Δ}
  → PEREnv η η'
  → {t t' : Γ ⊢⋆ K}
  → t ≡β t' → PER K (eval t η) (eval t' η')
fund p (refl≡β A) = idext p A
fund p (sym≡β q) = symPER _ (fund (symPER _ ∘ p) q)
fund p (trans≡β q r) = transPER _ (fund (reflPER _ ∘ p) q) (fund p r)
fund p (⇒≡β q r) = cong₂ _⇒_ (fund p q) (fund p r)
fund p (Π≡β q) = cong Π (fund (PER,,⋆ (renPER S ∘ p) (reflectPER _ refl)) q)
fund p (ƛ≡β {B = B}{B' = B'} q) =
  (λ ρ ρ' v v' r → transPER _ (renval-eval B (PER,,⋆ (renPER ρ ∘ reflPER _ ∘ p) r) ρ')
                     (idext (λ { Z → renPER ρ' (reflPER _ (symPER _ r))
                               ; (S x) → symPER _ (renval-comp ρ ρ' (reflPER _ (p x)))})
                            B))
  ,
  (λ ρ ρ' v v' r → transPER _
                     (renval-eval B' (PER,,⋆ (renPER ρ ∘ reflPER _ ∘ symPER _ ∘ p) r)
                      ρ')
                     (idext (λ { Z → renPER ρ' (reflPER _ (symPER _ r))
                            ; (S x) → symPER _ (renval-comp ρ ρ' (reflPER _ (symPER _ (p x))))}) B'))
  ,
  λ ρ r → fund (PER,,⋆ (renPER ρ ∘ p) r) q
fund p (·≡β q r) = PERApp (fund p q) (fund p r)
fund p (μ≡β q) = reflectPER _ (cong μ (reifyPER _ (fund (PER,,⋆ (renPER S ∘ p) (reflectPER _ refl)) q)))
fund p (β≡β B A) = transPER _  (idext (λ { Z → idext (reflPER _ ∘ p) A ; (S x) → renval-id (reflPER _ (p x))}) B) (symPER _ (subst-eval B (symPER _ ∘ p) (subst-cons ` A)))
fund p (con≡β q) = cong (con _) (fund p q)
\end{code}

constructing the identity PER

\begin{code}
idPER : ∀{Γ K} → (x : Γ ∋⋆ K) → PER K (idEnv Γ x) (idEnv Γ x)
idPER x = reflectPER _ refl
\end{code}

\begin{code}
completeness : ∀ {K Γ} {s t : Γ ⊢⋆ K} → s ≡β t → nf s ≡ nf t
completeness p = reifyPER _ (fund idPER p)
\end{code}
