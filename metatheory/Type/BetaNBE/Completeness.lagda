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

-- to get the completeness proof to go through we need an additional
-- property on function spaces called Unif(ormity).

CR : ∀{Φ} K → Val Φ K → Val Φ K → Set
CR #       n        n'        = n ≡ n'
CR *       n        n'        = n ≡ n'
CR (K ⇒ J) (inj₁ n) (inj₁ n') = n ≡ n' -- reify (inj₁ n) ≡ reify (inj₁ n')
CR (K ⇒ J) (inj₂ f) (inj₁ n') = ⊥
CR (K ⇒ J) (inj₁ n) (inj₂ f)  = ⊥
CR (K ⇒ J) (inj₂ f) (inj₂ f') =
  Unif f
  ×
  Unif f'
  ×
  ∀ {Ψ}
     → (ρ : Ren _ Ψ)
     → {v v' : Val Ψ K}
     → CR K v v'
       ---------------------------------------------------------
     → CR J (f ρ v) (f' ρ v')
  where
    -- Uniformity
    Unif : ∀{Φ K J} → (∀ {Ψ} → Ren Φ Ψ → Val Ψ K → Val Ψ J) → Set
    Unif {Φ}{K}{J} f = ∀{Ψ Ψ'}
      → (ρ : Ren Φ Ψ)
      → (ρ' : Ren Ψ Ψ')
      → (v v' : Val Ψ K)
      → CR K v v'
        --------————————————————————————————————————————————————————————————————
      → CR J (renameVal ρ' (f ρ v))
             (f (ρ' ∘ ρ) (renameVal ρ' v'))
\end{code}

CR is symmetric and transitive, it is not reflexive, but we if we
have a value that is related to something else by CR then we can
derive a reflexivity result for it.

\begin{code}
symCR : ∀{Φ K}{v v' : Val Φ K}
  → CR K v v'
    ---------------------------
  → CR K v' v
symCR {K = #}                        p              = sym p
symCR {K = *}                        p              = sym p
symCR {K = K ⇒ J} {inj₁ n} {inj₁ n'} p              = sym p
symCR {K = K ⇒ J} {inj₁ n} {inj₂ f'} ()
symCR {K = K ⇒ J} {inj₂ f} {inj₁ n'} ()
symCR {K = K ⇒ J} {inj₂ f} {inj₂ f'} (p , p' , p'') =
  p' , p , λ ρ q → symCR (p'' ρ (symCR q))

transCR : ∀{Φ K} {v v' v'' : Val Φ K}
  → CR K v v'
  → CR K v' v''
    ----------------------------------
  → CR K v v''
transCR {K = #}                                   p              q
  = trans p q
transCR {K = *}                                   p              q
  = trans p q
transCR {K = K ⇒ J} {inj₁ n} {inj₁ n'} {inj₁ n''} p              q
  = trans p q
transCR {K = K ⇒ J} {inj₁ n} {inj₁ n'} {inj₂ f''} p              ()
transCR {K = K ⇒ J} {inj₁ n} {inj₂ f'}            ()             q
transCR {K = K ⇒ J} {inj₂ f} {inj₁ n'}            ()             q
transCR {K = K ⇒ J} {inj₂ f} {inj₂ f'} {inj₁ n}   p              ()
transCR {K = K ⇒ J} {inj₂ f} {inj₂ f'} {inj₂ f''} (p , p' , p'') (q , q' , q'')
 = p , q' , λ ρ r → transCR (p'' ρ r) (q'' ρ (transCR (symCR r) r))

reflCR : ∀{Φ K}{v v' : Val Φ K}
  → CR K v v'
    ---------------------------
  → CR K v v
reflCR p = transCR p (symCR p)
\end{code}

reify takes two related values and produces to identical normal
forms. reflectCR works in the other direction for neutral terms. They
are not mutually defined in this version of NBE.

Composing reify with the fundamental theorem of CR defined later and
using reflectCR to build identify environments will give us the
completeness result.

\begin{code}
reflectCR : ∀{Φ K} → {n n' : Φ ⊢NeN⋆ K}
  → n ≡ n'
    -----------------------------
  → CR K (reflect n) (reflect n')
reflectCR {K = #}     p = cong ne p
reflectCR {K = *}     p = cong ne p
reflectCR {K = K ⇒ J} p = p

reifyCR : ∀{Φ K} → {v v' : Val Φ K}
  → CR K v v'
    -------------------------------
  → reify v ≡ reify v'
reifyCR {K = #    }                    p              = p
reifyCR {K = *    }                    p              = p
reifyCR {K = K ⇒ J} {inj₁ n} {inj₁ n'} p              = cong ne p
reifyCR {K = K ⇒ J} {inj₁ n} {inj₂ f'} ()             
reifyCR {K = K ⇒ J} {inj₂ f} {inj₁ n'} ()             
reifyCR {K = K ⇒ J} {inj₂ f} {inj₂ f'} (p , p' , p'') =
  cong ƛ (reifyCR (p'' S (reflectCR refl)))
\end{code}

'equality' for environements/CR lifted from values to environements

\begin{code}
EnvCR : ∀ {Φ Ψ} → (η η' : Env Φ Ψ) →  Set
EnvCR η η' = ∀{K}(α : _ ∋⋆ K) → CR K (η α) (η' α) 
\end{code}

Closure under environment extension

\begin{code}
CR,,⋆ : ∀{Φ Ψ K}{η η' : Env Φ Ψ}
  → EnvCR η η'
  → {v v' : Val Ψ K}
  → CR K v v'
    ----------------------------
  → EnvCR (η ,,⋆ v) (η' ,,⋆ v')
CR,,⋆ p q Z     = q
CR,,⋆ p q (S α) = p α
\end{code}

Closure under application

\begin{code}
AppCR : ∀{Φ K J}
  → {f f' : Val Φ (K ⇒ J)}
  → CR (K ⇒ J) f f'
  → {v v' : Val Φ K}
  → CR K v v'
  → CR J (f ·V v) (f' ·V v')
AppCR {f = inj₁ n} {inj₁ .n} refl           q =
  reflectCR (cong (n ·_) (reifyCR q))
AppCR {f = inj₁ n} {inj₂ f'} ()             q
AppCR {f = inj₂ f} {inj₁ n}  ()             q
AppCR {f = inj₂ f} {inj₂ f'} (p , p' , p'') q = p'' id q
\end{code}

renameVal commutes with reflect

\begin{code}
renameVal-reflect : ∀{Φ Ψ K}
  → (ρ : Ren Φ Ψ)
  → (n : Φ ⊢NeN⋆ K)
    --------------------------------------------------------
  → CR K (renameVal ρ (reflect n)) (reflect (renameNeN ρ n))
renameVal-reflect {K = #}     ρ n = refl
renameVal-reflect {K = *}     ρ n = refl
renameVal-reflect {K = K ⇒ J} ρ n = refl 
\end{code}

renaming commutes with reify

\begin{code}
rename-reify : ∀{K Φ Ψ}{v v' : Val Φ K}
  → CR K v v'
  → (ρ : Ren Φ Ψ)
    ---------------------------------------------
  → renameNf ρ (reify v) ≡ reify (renameVal ρ v')
rename-reify {#}                            refl           ρ = refl
rename-reify {*}                            refl           ρ = refl
rename-reify {K ⇒ J} {v = inj₁ n} {inj₁ .n} refl           ρ = refl
rename-reify {K ⇒ J} {v = inj₁ n} {inj₂ f'} ()             ρ
rename-reify {K ⇒ J} {v = inj₂ f} {inj₁ n'} ()             ρ
rename-reify {K ⇒ J} {v = inj₂ f} {inj₂ f'} (p , p' , p'') ρ = cong ƛ (trans (rename-reify (p'' S (reflectCR (refl {x = ` Z}))) (ext ρ)) (reifyCR (transCR ( p' S (ext ρ) _ _ (reflectCR refl) ) (AppCR {f = renameVal (S ∘ ρ) (inj₂ f')}{renameVal (S ∘ ρ) (inj₂ f')} ((λ ρ₁ ρ' v → p' (ρ₁ ∘ S ∘ ρ) ρ' v) , (λ ρ₁ ρ' v → p' (ρ₁ ∘ S ∘ ρ) ρ' v) , λ ρ' q → (proj₂ (proj₂ (reflCR (symCR (p , p' , p'')))) (ρ' ∘ S ∘ ρ) q)) (renameVal-reflect (ext ρ) (` Z))))))
\end{code}

first functor law for renameVal

\begin{code}
renameVal-id : ∀ {K Φ}{v v' : Val Φ K}
  → CR K v v'
    ------------------------
  → CR K (renameVal id v) v'
renameVal-id {#}                            refl = renameNf-id _
renameVal-id {*}                            refl = renameNf-id _
renameVal-id {K ⇒ J} {v = inj₁ n} {inj₁ n'} refl = renameNeN-id _
renameVal-id {K ⇒ J} {v = inj₁ n} {inj₂ f'} ()
renameVal-id {K ⇒ J} {v = inj₂ f} {inj₁ n'} () 
renameVal-id {K ⇒ J} {v = inj₂ f} {inj₂ f'} p    = p
\end{code}

second functor law for renameVal

\begin{code}
renameVal-comp : ∀ {K Φ Ψ Θ}
  → (ρ : Ren Φ Ψ)
  → (ρ' : Ren Ψ Θ)
  → {v v' : Val Φ K}
  → CR K v v'
  → CR K (renameVal (ρ' ∘ ρ) v) (renameVal ρ' (renameVal ρ v'))
renameVal-comp {#}      ρ ρ'                    refl           =
  renameNf-comp _
renameVal-comp {*}      ρ ρ'                    refl           =
  renameNf-comp _
renameVal-comp {K ⇒ K₁} ρ ρ' {inj₁ n} {inj₁ n'} refl           =
  renameNeN-comp _
renameVal-comp {K ⇒ K₁} ρ ρ' {inj₁ x} {inj₂ y} ()
renameVal-comp {K ⇒ K₁} ρ ρ' {inj₂ y} {inj₁ x} ()
renameVal-comp {K ⇒ K₁} ρ ρ' {inj₂ y} {inj₂ y₁} (p , p' , p'') =
  (λ ρ'' ρ''' v → p (ρ'' ∘ ρ' ∘ ρ) ρ''' v)
  ,
  (λ ρ'' ρ''' v → p' (ρ'' ∘ ρ' ∘ ρ) ρ''' v)
  ,
  λ ρ'' q → p'' (ρ'' ∘ ρ' ∘ ρ) q
\end{code}

CR is closed under renaming

\begin{code}
renCR : ∀{Φ Ψ K}{v v' : Val Φ K}
  → (ρ : Ren Φ Ψ)
  → CR K v v'
  → CR K (renameVal ρ v) (renameVal ρ v')
renCR {K = #}                         ρ p              = cong (renameNf ρ) p
renCR {K = *}                         ρ p              = cong (renameNf ρ) p
renCR {K = K ⇒ K₁} {inj₁ n} {inj₁ .n} ρ refl           = refl
renCR {K = K ⇒ K₁} {inj₁ n} {inj₂ f'} ρ ()
renCR {K = K ⇒ K₁} {inj₂ f} {inj₁ n'} ρ ()
renCR {K = K ⇒ K₁} {inj₂ f} {inj₂ f'} ρ (p , p' , p'') =
  (λ ρ' ρ'' v → p (ρ' ∘ ρ) ρ'' v)
  ,
  (λ ρ' ρ'' v → p' (ρ' ∘ ρ) ρ'' v)
  ,
  λ ρ' q → p'' (ρ' ∘ ρ) q
\end{code}

CR is closed under application
\begin{code}
renameVal·V : ∀{K J Φ Ψ}
  → (ρ : Ren Φ Ψ)
  → {f f' : Val Φ (K ⇒ J)}
  → CR (K ⇒ J) f f'
  → {v v' : Val Φ K}
  → CR K v v'
    --------------------------------------------------------------
  → CR J (renameVal ρ (f ·V v)) (renameVal ρ f' ·V renameVal ρ v')
renameVal·V {J = #} ρ {inj₁ n} {inj₁ .n} refl {v}{v'} q =
  cong (ne ∘ (renameNeN ρ n ·_))
       (trans ( rename-reify (reflCR q) ρ ) (reifyCR (renCR ρ q)))
renameVal·V {J = *} ρ {inj₁ n} {inj₁ .n} refl {v}{v'} q =
  cong (ne ∘ (renameNeN ρ n ·_))
       (trans ( rename-reify (reflCR q) ρ ) (reifyCR (renCR ρ q)))
renameVal·V {J = J ⇒ K} ρ {inj₁ n} {inj₁ .n} refl     q =
  cong (renameNeN ρ n ·_)
       (trans ( rename-reify (reflCR q) ρ ) (reifyCR (renCR ρ q)))
renameVal·V ρ {inj₁ n} {inj₂ f}  ()                   q
renameVal·V ρ {inj₂ f} {inj₁ n'} ()                   q
renameVal·V ρ {inj₂ f} {inj₂ f'} (p , p' , p'')       q =
  transCR (p id ρ _ _ q) (p'' ρ (renCR ρ (reflCR (symCR q))))
\end{code}

identity extension lemma, (post) renaming commutes with eval, defined mutually

\begin{code}
idext : ∀{Φ Ψ K}{η η' : Env Φ Ψ}
  → EnvCR η η'
  → (t : Φ ⊢⋆ K)
    ----------------------------
  → CR K (eval t η) (eval t η')

renameVal-eval : ∀{Φ Ψ Θ K}
  → (t : Ψ ⊢⋆ K)
  → {η η' : ∀{J} → Ψ ∋⋆ J → Val Φ J}
  → (p : EnvCR η η')
  → (ρ : Ren Φ Θ )
    ---------------------------------------------------------
  → CR K (renameVal ρ (eval t η)) (eval t (renameVal ρ ∘ η'))
  
idext p (` x)       = p x
idext p (Π B)       = cong Π (idext (CR,,⋆ (renCR S ∘ p) (reflectCR refl)) B)
idext p (A ⇒ B)     = cong₂ _⇒_ (idext p A) (idext p B)
idext p (ƛ B)       =
  (λ ρ ρ' v v' q →
    transCR (renameVal-eval B (CR,,⋆ (renCR ρ ∘ reflCR ∘ p) q) ρ')
            (idext (λ { Z     → renCR ρ' (reflCR (symCR q))
                      ; (S x) → symCR (renameVal-comp ρ ρ' (reflCR (p x)))})
                   B))
  ,
  (λ ρ ρ' v v' q →
    transCR
      (renameVal-eval B (CR,,⋆ (renCR ρ ∘ reflCR ∘ symCR ∘ p) q) ρ')
      (idext (λ { Z  → renCR ρ' (reflCR (symCR q))
                ; (S x) → symCR (renameVal-comp ρ ρ' (reflCR (symCR (p x))))})
             B)) -- first two terms are identical (except for symCR (p x))
  ,
  λ ρ q → idext (CR,,⋆ (renCR ρ ∘ p) q) B
idext p (A · B)     = AppCR (idext p A) (idext p B)
idext p μ1          = refl
idext p (size⋆ n)   = refl
idext p (con tcn s) = cong (con tcn) (idext p s)

renameVal-eval (` x) p ρ = renCR ρ (p x)
renameVal-eval (Π B) p ρ =
  cong Π (trans
    (renameVal-eval B
                    (CR,,⋆ (renCR S ∘ p) (reflectCR refl))
                    (ext ρ))
    (idext (λ{ Z     → renameVal-reflect (ext ρ) (` Z)
             ; (S x) → transCR
                  (symCR (renameVal-comp S (ext ρ) (reflCR (symCR (p x)))))
                  (renameVal-comp ρ S (reflCR (symCR (p x))))})
             B))
renameVal-eval (A ⇒ B) p ρ =
  cong₂ _⇒_ (renameVal-eval A p ρ) (renameVal-eval B p ρ)
renameVal-eval (ƛ B) {η}{η'} p ρ =
  (λ ρ' ρ'' v v' q →
    transCR (renameVal-eval B (CR,,⋆ (renCR (ρ' ∘ ρ) ∘ p) q) ρ'')
            (idext (λ { Z     → renCR ρ'' (reflCR (symCR q))
                      ; (S x) → symCR (renameVal-comp (ρ' ∘ ρ) ρ'' (p x))})
                   B))
  ,
  (λ ρ' ρ'' v v' q → transCR
    (renameVal-eval
      B
      (CR,,⋆ (renCR ρ' ∘ renCR ρ ∘ reflCR ∘ symCR ∘ p) q) ρ'')
    (idext (λ { Z     → renCR ρ'' (reflCR (symCR q))
              ; (S x) → symCR
                  (renameVal-comp ρ' ρ'' (renCR ρ (reflCR (symCR (p x)))))})
           B)) -- again two almost identical terms
  ,
  λ ρ' q → idext (λ { Z → q ; (S x) → renameVal-comp ρ ρ' (p x) }) B
renameVal-eval (A · B) p ρ = transCR
  (renameVal·V ρ (idext (reflCR ∘ p) A) (idext (reflCR ∘ p) B))
  (AppCR (renameVal-eval A p ρ) (renameVal-eval B p ρ))
renameVal-eval μ1          p ρ = refl
renameVal-eval (size⋆ n)   p ρ = refl
renameVal-eval (con tcn s) p ρ = cong (con tcn) (renameVal-eval s p ρ)
\end{code}

(pre) renaming commutes with eval

\begin{code}
rename-eval : ∀{Φ Ψ Θ K}
  (t : Θ ⊢⋆ K)
  {η η' : ∀{J} → Ψ ∋⋆ J → Val Φ J}
  (p : EnvCR η η')
  (ρ : Ren Θ Ψ) →
  CR K (eval (rename ρ t) η) (eval t (η' ∘ ρ))
rename-eval (` x) p ρ = p (ρ x)
rename-eval (Π B) p ρ =
  cong Π (trans (rename-eval
                  B
                  (CR,,⋆ (renCR S ∘ p)
                          (reflectCR (refl {x = ` Z}))) (ext ρ))
       (idext (λ{ Z     → reflectCR refl
                ; (S x) → (renCR S ∘ reflCR ∘ symCR ∘ p) (ρ x)}) B))
rename-eval (A ⇒ B) p ρ = cong₂ _⇒_ (rename-eval A p ρ) (rename-eval B p ρ) 
rename-eval (ƛ B) p ρ =
  (λ ρ' ρ'' v v' q → transCR
     (renameVal-eval (rename (ext ρ) B) (CR,,⋆ (renCR ρ' ∘ reflCR ∘ p) q) ρ'')
     (idext (λ { Z → renCR ρ'' (reflCR (symCR q))
               ; (S x) → symCR (renameVal-comp ρ' ρ'' (reflCR (p x)))})
            (rename (ext ρ) B)))
  ,
  (λ ρ' ρ'' v v' q → transCR
    (renameVal-eval B (CR,,⋆ (renCR ρ' ∘ reflCR ∘ symCR ∘ p ∘ ρ) q) ρ'')
    (idext (λ { Z     →  renCR ρ'' (reflCR (symCR q))
              ; (S x) → symCR
                   (renameVal-comp ρ' ρ'' (reflCR (symCR (p (ρ x)))))})
           B))
  ,
  λ ρ' q → transCR
    (rename-eval B (CR,,⋆ (renCR ρ' ∘ p) q) (ext ρ))
    (idext (λ { Z     → reflCR (symCR q)
              ; (S x) → renCR ρ' (reflCR (symCR (p (ρ x)))) }) B)
rename-eval (A · B) p ρ = AppCR (rename-eval A p ρ) (rename-eval B p ρ)
rename-eval μ1          p ρ = refl
rename-eval (size⋆ n)   p ρ = refl
rename-eval (con tcn s) p ρ = cong (con tcn) (rename-eval s p ρ)
\end{code}

Subsitution lemma

\begin{code}
subst-eval : ∀{Φ Ψ Θ K}
  (t : Θ ⊢⋆ K)
  {η η' : ∀{J} → Ψ ∋⋆ J → Val Φ J}
  (p : EnvCR η η')
  (σ : Sub Θ Ψ) →
  CR K (eval (subst σ t) η) (eval t (λ x → eval (σ x) η'))
subst-eval (` x)      p σ = idext p (σ x)
subst-eval (Π B)      p σ = cong Π (trans
  (subst-eval B (CR,,⋆ (renCR S ∘ p) (reflectCR (refl {x = ` Z}))) (exts σ))
  (idext (λ{ Z     → reflectCR (refl {x = ` Z})
           ; (S x) → transCR
                (rename-eval
                  (σ x)
                  (CR,,⋆ (renCR S ∘ reflCR ∘ symCR ∘ p) (reflectCR refl)) S)
                (symCR (renameVal-eval (σ x)  (reflCR ∘ symCR ∘ p) S)) })
         B))
subst-eval (A ⇒ B)    p σ = cong₂ _⇒_ (subst-eval A p σ) (subst-eval B p σ)
subst-eval (ƛ B)      p σ =
  (λ ρ ρ' v v' q → transCR
     (renameVal-eval (subst (exts σ) B) (CR,,⋆ (renCR ρ ∘ reflCR ∘ p) q) ρ')
     (idext (λ { Z     → renCR ρ' (reflCR (symCR q))
               ; (S x) → symCR (renameVal-comp ρ ρ' (reflCR (p x)))})
            (subst (exts σ) B)))
  ,
  (λ ρ ρ' v v' q → transCR
    (renameVal-eval B (CR,,⋆ (renCR ρ ∘ idext (reflCR ∘ symCR ∘ p) ∘ σ) q) ρ')
    (idext (λ { Z → renCR ρ' (reflCR (symCR q))
              ; (S x) → symCR
                   (renameVal-comp ρ ρ' (idext (reflCR ∘ symCR ∘ p) (σ x)))})
           B))
  ,
  λ ρ q → transCR (subst-eval B (CR,,⋆ (renCR ρ ∘ p) q) (exts σ))
    (idext (λ { Z     → reflCR (symCR q)
              ; (S x) → transCR
                   (rename-eval
                     (σ x)
                     (CR,,⋆ (renCR ρ ∘ reflCR ∘ symCR ∘ p) (reflCR (symCR q)))
                     S)
                   (symCR (renameVal-eval (σ x) (reflCR ∘ symCR ∘ p) ρ))})
           B)
subst-eval (A · B)    p σ = AppCR (subst-eval A p σ) (subst-eval B p σ)
subst-eval μ1          p ρ = refl                 
subst-eval (size⋆ n)   p ρ = refl
subst-eval (con tcn s) p ρ = cong (con tcn) (subst-eval s p ρ)
\end{code}

Fundamental Theorem of logical relations for CR

\begin{code}
fund : ∀{Φ Ψ K}{η η' : Env Φ Ψ}
  → EnvCR η η'
  → {t t' : Φ ⊢⋆ K}
  → t ≡β t' → CR K (eval t η) (eval t' η')
fund p (refl≡β A)          = idext p A
fund p (sym≡β q)           = symCR (fund (symCR ∘ p) q)
fund p (trans≡β q r)       = transCR (fund (reflCR ∘ p) q) (fund p r)
fund p (⇒≡β q r)           = cong₂ _⇒_ (fund p q) (fund p r)
fund p (Π≡β q)             =
  cong Π (fund (CR,,⋆ (renCR S ∘ p) (reflectCR refl)) q)
fund p (ƛ≡β {B = B}{B'} q) =
  (λ ρ ρ' v v' r → transCR
    (renameVal-eval B (CR,,⋆ (renCR ρ ∘ reflCR ∘ p) r) ρ')
    (idext (λ { Z → renCR ρ' (reflCR (symCR r))
              ; (S x) → symCR (renameVal-comp ρ ρ' (reflCR (p x)))})
           B))
  ,
  (λ ρ ρ' v v' r → transCR
     (renameVal-eval B' (CR,,⋆ (renCR ρ ∘ reflCR ∘ symCR ∘ p) r) ρ')
     (idext (λ { Z → renCR ρ' (reflCR (symCR r))
               ; (S x) → symCR (renameVal-comp ρ ρ' (reflCR (symCR (p x))))})
            B'))
  ,
  λ ρ r → fund (CR,,⋆ (renCR ρ ∘ p) r) q
fund p (·≡β q r) = AppCR (fund p q) (fund p r)
fund p (β≡β B A) =
  transCR (idext (λ { Z     → idext (reflCR ∘ p) A
                    ; (S x) → renameVal-id (reflCR (p x))})
                 B)
          (symCR (subst-eval B (symCR ∘ p) (subst-cons ` A)))
fund p (con≡β q) = cong (con _) (fund p q)
\end{code}

constructing the identity CR

\begin{code}
idCR : ∀{Φ K} → (x : Φ ∋⋆ K) → CR K (idEnv Φ x) (idEnv Φ x)
idCR x = reflectCR refl
\end{code}

\begin{code}
completeness : ∀ {K Φ} {s t : Φ ⊢⋆ K} → s ≡β t → nf s ≡ nf t
completeness p = reifyCR (fund idCR p)
\end{code}
