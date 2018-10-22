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
open import Data.Unit
open import Function
\end{code}

\begin{code}
mutual
  -- A Partial equivalence relation on values: 'equality on values'
  PER : ∀{Γ} K → Val Γ K → Val Γ K → Set
  PER size    n n' = n ≡ n'
  PER *       n n' = n ≡ n' -- the same as readback n ≡ readback n'
  PER (K ⇒ J) (inj₁ n) (inj₁ n') = readback (inj₁ n) ≡ readback (inj₁ n')
  PER (K ⇒ J) (inj₂ f) (inj₁ n') = ⊥ -- A semantic function cannot be beta-equal to a neutral
  PER (K ⇒ J) (inj₁ n) (inj₂ f)  = ⊥ -- A semantic function cannot be beta-equal to a neutral
  PER (K ⇒ J) (inj₂ f) (inj₂ f') =
   Unif (inj₂ f)
   ×
   Unif (inj₂ f')
   ×
   ∀ {Δ}
     → (ρ : Ren _ Δ)
     → {v v' : Val Δ K}
     → PER K v v'
     → PER J (renval ρ (inj₂ f) ·V v) (renval ρ (inj₂ f') ·V v')

  Unif : ∀{Γ K J} → Val Γ (K ⇒ J) → Set
  Unif {Γ}{K}{J} f = ∀{Δ Δ'}(ρ : Ren Γ Δ)(ρ' : Ren Δ Δ')(v v' : Val Δ K) → PER K v v'
    → PER J  (renval ρ' (renval ρ f ·V v)) (renval (ρ' ∘ ρ) f ·V renval ρ' v')

transPER : ∀{Γ} K {v v' v'' : Val Γ K} → PER K v v' → PER K v' v'' → PER K v v''

symPER : ∀{Γ} K {v v' : Val Γ K} → PER K v v' → PER K v' v
symPER size                       p = sym p
symPER *                          p = sym p
symPER (K ⇒ J) {inj₁ n} {inj₁ n'} p = sym p
symPER (K ⇒ J) {inj₁ n} {inj₂ f'} ()
symPER (K ⇒ J) {inj₂ f} {inj₁ n'} ()
symPER (K ⇒ J) {inj₂ f} {inj₂ f'} (p , p' , p'') = p' , p , λ ρ q → symPER J (p'' ρ (symPER K q))

transPER size                                  p q = trans p q
transPER *                                     p q = trans p q
transPER (K ⇒ J) {inj₁ n} {inj₁ n'} {inj₁ n''} p q = trans p q
transPER (K ⇒ J) {inj₁ n} {inj₁ n'} {inj₂ f''} p ()
transPER (K ⇒ J) {inj₁ n} {inj₂ f'} () q
transPER (K ⇒ J) {inj₂ f} {inj₁ n'} () q
transPER (K ⇒ J) {inj₂ f} {inj₂ f'} {inj₁ n} p ()
transPER (K ⇒ J) {inj₂ f} {inj₂ f'} {inj₂ f''} (p , p' , p'') (q , q' , q'') = p , q' , λ ρ r → transPER J (p'' ρ r) (q'' ρ (transPER K (symPER K r) r))

reflPER : ∀{Γ} K {v v' : Val Γ K} → PER K v v' → PER K v v
reflPER K p = transPER K p (symPER K p)
\end{code}

\begin{code}

reflect : ∀{Γ} K → {n n' : Γ ⊢NeN⋆ K}
  → n ≡ n' → PER K (neV n) (neV n')
reflect size    p = cong ne p
reflect *       p = cong ne p
reflect (K ⇒ J) p = cong ne p


reify : ∀{Γ} K → {v v' : Val Γ K}
  → PER K v v' → readback v ≡ readback v'
reify size                       p = p
reify *                          p = p
reify (K ⇒ J) {inj₁ n} {inj₁ n'} p = p
reify (K ⇒ J) {inj₁ n} {inj₂ f'} ()
reify (K ⇒ J) {inj₂ f} {inj₁ n'} ()
reify (K ⇒ J) {inj₂ f} {inj₂ f'} (p , p' , p'') =
  cong ƛ (reify J (p'' S (reflect K refl)))
\end{code}

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
  → PEREnv (η ,,⋆ v) (η' ,,⋆ v')
PER,,⋆ p q Z = q
PER,,⋆ p q (S x) = p x
\end{code}

Closure under applicatoin
\begin{code}
PERApp : ∀{Γ K J}
  → {f f' : Val Γ (K ⇒ J)}
  → PER (K ⇒ J) f f'
  → {v v' : Val Γ K}
  → PER K v v'
  → PER J (f ·V v) (f' ·V v')
PERApp {f = inj₁ n} {inj₁ .n} refl q = reflect _ (cong (n ·_) (reify _ q))
PERApp {f = inj₁ n} {inj₂ f'} () q
PERApp {f = inj₂ f} {inj₁ n} () q
PERApp {f = inj₂ f} {inj₂ f'} (p , p' , p'') q = p'' id q
\end{code}

\begin{code}
renval-ext : ∀{K Γ Δ}(ρ : Ren Γ Δ) → PER K (renval (ext ρ) (neV (` Z))) (neV (` Z))
renval-ext {size}  ρ = refl
renval-ext {*}     ρ = refl
renval-ext {K ⇒ J} ρ = refl
\end{code}

\begin{code}
rename-readback : ∀{K Γ Δ}{v v' : Val Γ K} → PER K v v' → (ρ : Ren Γ Δ) → renameNf ρ (readback v) ≡ readback (renval ρ v')
rename-readback {size}                         refl           ρ = refl
rename-readback {*}                            refl           ρ = refl
rename-readback {K ⇒ J} {v = inj₁ n} {inj₁ .n} refl           ρ = refl
rename-readback {K ⇒ J} {v = inj₁ n} {inj₂ f'} ()             ρ
rename-readback {K ⇒ J} {v = inj₂ f} {inj₁ n'} ()             ρ
rename-readback {K ⇒ J} {v = inj₂ f} {inj₂ f'} (p , p' , p'') ρ = cong ƛ (trans
                                                                            (rename-readback (p'' S (reflect K (refl {x = ` Z}))) (ext ρ)) (reify J (transPER J ( p' S (ext ρ) _ _ (reflect K refl) ) (PERApp {f = renval (S ∘ ρ) (inj₂ f')}{renval (S ∘ ρ) (inj₂ f')} ((λ ρ₁ ρ' v → p' (ρ₁ ∘ S ∘ ρ) ρ' v) , (λ ρ₁ ρ' v → p' (ρ₁ ∘ S ∘ ρ) ρ' v) , λ ρ' q → (proj₂ (proj₂ (reflPER (K ⇒ J) (symPER (K ⇒ J) (p , p' , p'')))) (ρ' ∘ S ∘ ρ) q)) (renval-ext ρ)))))


\end{code}

\begin{code}
renval-id : ∀ {K Γ}{v v' : Val Γ K} →
  PER K v v' → 
  PER K (renval id v) v'
renval-id {size}                         refl = renameNf-id _
renval-id {*}                            refl = renameNf-id _
renval-id {K ⇒ J} {v = inj₁ n} {inj₁ n'} refl = cong ne (renameNeN-id _)
renval-id {K ⇒ J} {v = inj₁ n} {inj₂ f'} ()
renval-id {K ⇒ J} {v = inj₂ f} {inj₁ n'} () 
renval-id {K ⇒ J} {v = inj₂ f} {inj₂ f'} p    = p
\end{code}

\begin{code}

renval-comp : ∀ {K Γ Δ Θ}(ρ : Ren Γ Δ)(ρ' : Ren Δ Θ){v v' : Val Γ K} →
  PER K v v' → 
  PER K (renval (ρ' ∘ ρ) v) (renval ρ' (renval ρ v'))
renval-comp {size}   ρ ρ'                    refl           =
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

Closure under renaming
\begin{code}
renPER : ∀{Γ Δ K}{v v' : Val Γ K}
  → (ρ : Ren Γ Δ)
  → PER K v v'
  → PER K (renval ρ v) (renval ρ v')
renPER {K = size}                      ρ p              = cong (renameNf ρ) p
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

\begin{code}
renval-neV : ∀{Γ Δ K}(ρ : Ren Γ Δ)(n : Γ ⊢NeN⋆ K) → PER K (renval ρ (neV n)) (neV (renameNeN ρ n))
renval-neV {K = size}  ρ n = refl
renval-neV {K = *}     ρ n = refl
renval-neV {K = K ⇒ J} ρ n = refl 
\end{code}

-- completeness

identity extension lemma/a congruence for eval
\begin{code}
renval·V : ∀{K J Γ Δ}
  (ρ : Ren Γ Δ)
  {f f' : Val Γ (K ⇒ J)}
  → PER (K ⇒ J) f f'
  → {v v' : Val Γ K}
  → PER K v v'
  → PER J (renval ρ (f ·V v)) (renval ρ f' ·V renval ρ v')
renval·V {J = size} ρ {inj₁ n} {inj₁ .n} refl {v}{v'} q = cong (ne ∘ (renameNeN ρ n ·_)) (trans ( rename-readback (reflPER _ q) ρ ) (reify _ (renPER ρ q)))
renval·V {J = *} ρ {inj₁ n} {inj₁ .n} refl {v}{v'} q = cong (ne ∘ (renameNeN ρ n ·_)) (trans ( rename-readback (reflPER _ q) ρ ) (reify _ (renPER ρ q)))
renval·V {J = J ⇒ K} ρ {inj₁ n} {inj₁ .n} refl {v}{v'} q = cong (ne ∘ (renameNeN ρ n ·_)) (trans ( rename-readback (reflPER _ q) ρ ) (reify _ (renPER ρ q)))
renval·V ρ {inj₁ n} {inj₂ f} () q
renval·V ρ {inj₂ f} {inj₁ n'} () q
renval·V ρ {inj₂ f} {inj₂ f'} (p , p' , p'') q = transPER _ (p id ρ _ _ q) (p'' ρ (renPER ρ (reflPER _ (symPER _ q))))

idext : ∀{Γ Δ K}{η η' : Env Γ Δ}
  → PEREnv η η'
  → (t : Γ ⊢⋆ K)
  → PER K (eval t η) (eval t η')

renval-eval : ∀{Γ Δ Θ K}
  (t : Δ ⊢⋆ K)
  {η η' : ∀{J} → Δ ∋⋆ J → Val Γ J}
  (p : PEREnv η η')
  (ρ : Ren Γ Θ ) →
  PER K (renval ρ (eval t η)) (eval t (renval ρ ∘ η'))
renval-eval (` x) p ρ = renPER ρ (p x)
renval-eval (Π B) p ρ = cong Π (trans (renval-eval B (PER,,⋆ (renPER S ∘ p) (reflect _ (refl {x = ` Z}))) (ext ρ)) (idext (λ{ Z → renval-ext ρ ; (S x) → transPER _ (symPER _ (renval-comp S (ext ρ) (reflPER _ (symPER _ (p x))))) (renval-comp ρ S (reflPER _ (symPER _ (p x))))}) B))
renval-eval (A ⇒ B) p ρ = cong₂ _⇒_ (renval-eval A p ρ) (renval-eval B p ρ)
renval-eval (ƛ B) {η}{η'} p ρ =
  (λ ρ' ρ'' v v' q → transPER _ (renval-eval B (PER,,⋆ (renPER (ρ' ∘ ρ) ∘ p) q) ρ'') (idext (λ { Z → renPER ρ'' (reflPER _ (symPER _ q)) ; (S x) → symPER _ (renval-comp (ρ' ∘ ρ) ρ'' (p x))}) B))
  ,
  (λ ρ' ρ'' v v' q → transPER _ (renval-eval B (PER,,⋆ (renPER ρ' ∘ renPER ρ ∘ reflPER _ ∘ symPER _ ∘ p) q) ρ'') (idext (λ { Z → renPER ρ'' (reflPER _ (symPER _ q)) ; (S x) → symPER _ (renval-comp ρ' ρ'' (renPER ρ (reflPER _ (symPER _ (p x)))))}) B))
  ,
  λ ρ' q → idext (λ { Z → q ; (S x) → renval-comp ρ ρ' (p x) }) B
renval-eval (A · B) p ρ = transPER _ (renval·V ρ (idext (reflPER _ ∘ p) A) (idext (reflPER _ ∘ p) B)) (PERApp (renval-eval A p ρ) (renval-eval B p ρ))
renval-eval (μ B) p ρ = transPER _ (renval-neV ρ _) (reflect _ (cong μ (trans (rename-readback (idext (PER,,⋆ (renPER S ∘ reflPER _ ∘ p) (reflect _ refl)) B) (ext ρ)) (reify _ (transPER _ (renval-eval B (PER,,⋆ (renPER S ∘ p) (reflect _ refl)) (ext ρ)) (idext (λ { Z → renval-neV (ext ρ) (` Z) ; (S x) → transPER _ (symPER _ (renval-comp S (ext ρ) (p x))) (renval-comp ρ S (p x)) }) B))))))

idext p (` x)   = p x
idext p (Π B)   = cong Π (idext (PER,,⋆ (renPER S ∘ p) (reflect _ refl)) B)
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
idext p (μ  B)   = reflect _ (cong μ (reify _ (idext (PER,,⋆ (renPER S ∘ p) (reflect _ refl)) B)))
\end{code}

Renaming lemma
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
                          (reflect _ (refl {x = ` Z}))) (ext ρ))
       (idext (λ{ Z     → reflect _ refl
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
rename-eval (μ B) p ρ = reflect _ (cong μ (reify _ (transPER _ (rename-eval B (PER,,⋆ (renPER S ∘ p) (reflect _ refl)) (ext ρ)) (idext (λ { Z → reflect _ refl ; (S x) → renPER S ((reflPER _ ∘ symPER _ ∘ p) (ρ x))}) B))))
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
subst-eval (Π B) p σ = cong Π (trans (subst-eval B (PER,,⋆ (renPER S ∘ p) (reflect _ (refl {x = ` Z}))) (exts σ)) (idext (λ{ Z → reflect _ (refl {x = ` Z}) ; (S x) → transPER _ (rename-eval (σ x) (PER,,⋆ (renPER S ∘ reflPER _ ∘ symPER _ ∘ p) (reflect _ (refl {x = ` Z}))) S) (symPER _ (renval-eval (σ x)  (reflPER _ ∘ symPER _ ∘ p) S)) }) B))
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
subst-eval (μ B) p σ = reflect _ (cong μ (reify _ (transPER _ (subst-eval B (PER,,⋆ (renPER S ∘ p) (reflect _ refl)) (exts σ)) (idext (λ { Z → reflect _ refl ; (S x) → transPER _ (rename-eval (σ x) (PER,,⋆ (renPER S ∘ reflPER _ ∘ symPER _ ∘ p) (reflect _ refl)) S) (symPER _ (renval-eval (σ x) (reflPER _ ∘ symPER _ ∘ p) S))}) B))))
\end{code}


\begin{code}
fund : ∀{Γ Δ K}{η η' : Env Γ Δ}
  → PEREnv η η'
  → {t t' : Γ ⊢⋆ K}
  → t ≡β t' → PER K (eval t η) (eval t' η')
fund p (refl≡β A) = idext p A
fund p (sym≡β q) = symPER _ (fund (symPER _ ∘ p) q)
fund p (trans≡β q r) = transPER _ (fund (reflPER _ ∘ p) q) (fund p r)
fund p (⇒≡β q r) = cong₂ _⇒_ (fund p q) (fund p r)
fund p (Π≡β q) = cong Π (fund (PER,,⋆ (renPER S ∘ p) (reflect _ refl)) q)
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
fund p (μ≡β q) = reflect _ (cong μ (reify _ (fund (PER,,⋆ (renPER S ∘ p) (reflect _ refl)) q)))
fund p (β≡β{B = B}{A = A}) = transPER _  (idext (λ { Z → idext (reflPER _ ∘ p) A ; (S x) → renval-id (reflPER _ (p x))}) B) (symPER _ (subst-eval B (symPER _ ∘ p) (subst-cons ` A)))  
\end{code}

\begin{code}
idPER : ∀{Γ K} → (x : Γ ∋⋆ K) → PER K (idEnv Γ x) (idEnv Γ x)
idPER {K = size}  x = refl
idPER {K = *}     x = refl
idPER {K = K ⇒ J} x = refl
\end{code}

\begin{code}
completeness : ∀ {K Γ} {s t : Γ ⊢⋆ K} → s ≡β t → nf s ≡ nf t
completeness p = reify _ (fund idPER p)
\end{code}
