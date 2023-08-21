\begin{code}
module Algorithmic.RenamingSubstitution where
\end{code}

## Imports

\begin{code}
open import Function using (id; _∘_)
open import Data.Nat using (suc;zero)
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec as Vec using (Vec;[];_∷_;lookup) 
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;trans;cong;cong₂;subst)

open import Utils using (Kind;*)
open import Utils.List using (List;[];_∷_)
open import Type using (Ctx⋆;_,⋆_;S)
import Type.RenamingSubstitution as ⋆
open import Type.BetaNBE
open import Type.BetaNormal --using (_⊢Nf⋆_;_⊢Ne⋆_;renNf;weakenNf;renNf-VecList;renNf-List;lookup-renNf-VecList;embNf-List;embNf;embNf-VecList)
open _⊢Nf⋆_
open _⊢Ne⋆_

open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic using (Ctx;_∋_;conv∋;_⊢_;conv⊢;ConstrArgs;Cases;[];_∷_)
open import Algorithmic.Signature using (btype-ren;btype-sub)
open Ctx
open _∋_
open _⊢_

open import Type.BetaNormal.Equality using (renNf-id)
\end{code}

## Renaming

\begin{code}
Ren : ∀{Φ Ψ} → ⋆.Ren Φ Ψ → Ctx Φ → Ctx Ψ → Set
Ren ρ⋆ Γ Δ = {A : _ ⊢Nf⋆ *} → Γ ∋ A → Δ ∋ renNf ρ⋆ A

ext : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : Ren ρ⋆ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
    -------------------------------
  → Ren ρ⋆ (Γ , B) (Δ , renNf ρ⋆ B)
ext ρ⋆ ρ Z     = Z
ext ρ⋆ ρ (S x) = S (ρ x)

\end{code}

\begin{code}
ext⋆ : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : Ren ρ⋆ Γ Δ)
  → ∀ {K}
    --------------------------------
  → Ren (⋆.ext ρ⋆) (Γ ,⋆ K) (Δ ,⋆ K)
ext⋆ ρ⋆ ρ (T {A = A} x) = conv∋
  refl
  (weakenNf-renNf ρ⋆ A)
  (T (ρ x))
\end{code}

A property showing that renaming and the creating the case type is the same as 
creating the case type and the renaming.

\begin{code}
ren-mkCaseType : ∀ {Φ Ψ} 
           → (ρ⋆ : ⋆.Ren Φ Ψ)
           → ∀{A} AS 
           → renNf ρ⋆ (Algorithmic.mkCaseType A AS) ≡ Algorithmic.mkCaseType (renNf ρ⋆ A) (renNf-List ρ⋆ AS)
ren-mkCaseType ρ⋆ [] = refl
ren-mkCaseType ρ⋆ (x ∷ AS) = cong (renNf ρ⋆ x ⇒_) (ren-mkCaseType ρ⋆ AS)
\end{code}

The actual renaming definition

\begin{code}
ren : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : Ren ρ⋆ Γ Δ)
    -----------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Δ ⊢ renNf ρ⋆ A )

ren-ConstrArgs : ∀ {Φ Ψ Γ Δ n}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : Ren ρ⋆ Γ Δ)
  → (e : Fin n)
  → (A : Vec (List (Φ ⊢Nf⋆ *)) n)
  → (x : ConstrArgs Γ (lookup A e))
    --------------------------------------------
  → ConstrArgs Δ (lookup (renNf-VecList ρ⋆ A) e)

ren-ConstrArgs-List : ∀ {Φ Ψ Γ Δ}
  → (ρ⋆ : ⋆.Ren Φ Ψ)
  → (ρ : Ren ρ⋆ Γ Δ)
  → {AS : List (Φ ⊢Nf⋆ *) } 
  → (x : ConstrArgs Γ AS)
    -------------------------------
  → ConstrArgs Δ (renNf-List ρ⋆ AS)

ren-Cases : ∀ {Φ Ψ Γ Δ n} 
         → (ρ⋆ : ⋆.Ren Φ Ψ)
         → (ρ : Ren ρ⋆ Γ Δ)
         → {A : Φ ⊢Nf⋆ *} 
         → {tss : Vec (List (Φ ⊢Nf⋆ *)) n}
         → (cases : Cases Γ A tss)
          -------------------------------------------
         → Cases Δ (renNf ρ⋆ A) (renNf-VecList ρ⋆ tss)

ren ρ⋆ ρ (` x)             = ` (ρ x)
ren ρ⋆ ρ (ƛ N)             = ƛ (ren ρ⋆ (ext ρ⋆ ρ) N)
ren ρ⋆ ρ (L · M)           = ren ρ⋆ ρ L · ren ρ⋆ ρ M 
ren ρ⋆ ρ (Λ N)             = Λ (ren (⋆.ext ρ⋆) (ext⋆ ρ⋆ ρ) N)
ren ρ⋆ ρ (_·⋆_/_ {B = B} t A refl) = conv⊢
  refl
  (sym (ren[]Nf ρ⋆ B A))
  (ren ρ⋆ ρ t ·⋆ renNf ρ⋆ A / refl)
ren ρ⋆ ρ (wrap A B M)       = wrap
  (renNf ρ⋆ A)
  (renNf ρ⋆ B)
  (conv⊢ refl (ren-nf-μ ρ⋆ A B) (ren ρ⋆ ρ M))
ren ρ⋆ ρ (unwrap {A = A}{B} M refl) = conv⊢
  refl
  (sym (ren-nf-μ ρ⋆ A B))
  (unwrap (ren ρ⋆ ρ M) refl) 
ren ρ⋆ ρ (con {A} c refl)    = con c (subNf∅-renNf ρ⋆ A)
ren ρ⋆ ρ (builtin b / refl)  = conv⊢ refl (btype-ren b ρ⋆) (builtin b / refl)
ren ρ⋆ ρ (error A)           = error (renNf ρ⋆ A)
ren ρ⋆ ρ (constr e A refl x) = constr e (renNf-VecList ρ⋆ A) refl (ren-ConstrArgs ρ⋆ ρ e A x)
ren ρ⋆ ρ (case x cases)      = case (ren ρ⋆ ρ x) (ren-Cases ρ⋆ ρ cases)

ren-ConstrArgs-List ρ⋆ ρ [] = []
ren-ConstrArgs-List ρ⋆ ρ (t ∷ xs) = ren ρ⋆ ρ t ∷ ren-ConstrArgs-List ρ⋆ ρ xs

ren-ConstrArgs ρ⋆ ρ e A x 
          rewrite lookup-renNf-VecList ρ⋆ e A = ren-ConstrArgs-List ρ⋆ ρ x

ren-Cases ρ⋆ ρ [] = []
ren-Cases {Δ = Δ} ρ⋆ ρ {tss = AS ∷ _} (c ∷ cases) =   subst (Δ ⊢_) 
                                                            (ren-mkCaseType ρ⋆ AS) 
                                                            (ren ρ⋆ ρ c) 
                                                    ∷ (ren-Cases ρ⋆ ρ cases)
\end{code}

\begin{code}
weaken : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}{B : Φ ⊢Nf⋆ *}
  → Γ ⊢ A
    ---------
  → Γ , B ⊢ A
weaken t = conv⊢
  refl
  (renNf-id _)
  (ren id (conv∋ refl (sym (renNf-id _)) ∘ S) t)
\end{code}

\begin{code}
weaken⋆ : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}{K}
  → Γ ⊢ A
    ------------------
  → Γ ,⋆ K ⊢ weakenNf A
weaken⋆ t = ren S (λ α → _∋_.T α) t
\end{code}

## Substitution

\begin{code}
Sub : ∀{Φ Ψ} → SubNf Φ Ψ → Ctx Φ → Ctx Ψ → Set
Sub σ⋆ Γ Δ = (∀ {A : _ ⊢Nf⋆ *} → Γ ∋ A → Δ ⊢ subNf σ⋆ A)

exts : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
    ---------------------------------
  → Sub σ⋆ (Γ , B) (Δ , subNf σ⋆ B)
exts σ⋆ σ Z     = ` Z
exts σ⋆ σ (S α) = weaken (σ α)
\end{code}

\begin{code}
exts⋆ : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → ∀ {K}
    --------------------------------
  → Sub (extsNf σ⋆) (Γ ,⋆ K) (Δ ,⋆ K)
exts⋆ σ⋆ σ {K}(T {A = A} x) = conv⊢
  refl
  (weakenNf-subNf σ⋆ A)
  (weaken⋆ (σ x))
\end{code}

\begin{code}
sub : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
    -------------------------------------------
  → ({A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Δ ⊢ subNf σ⋆ A)

sub-ConstrList : ∀ {Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → {A : List (Φ ⊢Nf⋆ *)}
  → (x : ConstrArgs Γ A)
    --------------------------
  → ConstrArgs Δ (eval-List (⋆.sub-List (λ x₁ → embNf (σ⋆ x₁)) (embNf-List A)) (λ x₁ → reflect (` x₁)))
sub-ConstrList σ⋆ σ [] = []
sub-ConstrList σ⋆ σ (t ∷ xs) = sub σ⋆ σ t ∷ sub-ConstrList σ⋆ σ xs

sub-VecList : ∀ {Φ Ψ Γ Δ n}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → (e : Fin n) 
  → (A : Vec (List (Φ ⊢Nf⋆ *)) n)
  → (x : ConstrArgs Γ (lookup A e))
    --------------------------------------
  → ConstrArgs Δ (lookup (eval-VecList (⋆.sub-VecList (λ x₁ → embNf (σ⋆ x₁)) (embNf-VecList A)) (idEnv Ψ)) e)
sub-VecList σ⋆ σ e A x rewrite lookup-eval-VecList e (⋆.sub-VecList (λ x₁ → embNf (σ⋆ x₁)) (embNf-VecList A)) (idEnv _) 
                             | ⋆.lookup-sub-VecList (λ x₁ → embNf (σ⋆ x₁)) e (embNf-VecList A)  
                             | lookup-embNf-VecList e A = sub-ConstrList σ⋆ σ x

sub-mkCaseType : ∀ {Φ Ψ} 
           → (σ⋆ : SubNf Φ Ψ)
           → ∀{A} AS 
           →    subNf σ⋆ (Algorithmic.mkCaseType A AS) 
             ≡  Algorithmic.mkCaseType (subNf σ⋆ A) (eval-List (⋆.sub-List (λ x₁ → embNf (σ⋆ x₁)) (embNf-List AS)) (idEnv Ψ))
sub-mkCaseType σ⋆ [] = refl
sub-mkCaseType σ⋆ (x ∷ AS) = cong (subNf σ⋆ x ⇒_) (sub-mkCaseType σ⋆ AS) 

sub-Cases : ∀ {Φ Ψ Γ Δ n}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → {A : Φ ⊢Nf⋆ *}
  → {tss : Vec (List (Φ ⊢Nf⋆ *)) n}
  → (cs : Cases Γ A tss)
    ---------------------------------
  → Cases Δ (subNf σ⋆ A) (eval-VecList (⋆.sub-VecList (λ x₁ → embNf (σ⋆ x₁)) (embNf-VecList tss)) (idEnv Ψ))
sub-Cases σ⋆ σ [] = []
sub-Cases {Δ = Δ} σ⋆ σ {tss = AS ∷ _} (c ∷ cs) =    subst (Δ ⊢_) 
                                                          (sub-mkCaseType σ⋆ AS) 
                                                          (sub σ⋆ σ c) 
                                                  ∷ (sub-Cases σ⋆ σ cs)                            

sub σ⋆ σ (` k)                     = σ k
sub σ⋆ σ (ƛ N)                     = ƛ (sub σ⋆ (exts σ⋆ σ) N)
sub σ⋆ σ (L · M)                   = sub σ⋆ σ L · sub σ⋆ σ M
sub σ⋆ σ (Λ {B = B} N) =
  Λ (conv⊢ refl (sub-nf-Π σ⋆ B) (sub (extsNf σ⋆) (exts⋆ σ⋆ σ) N))
sub σ⋆ σ (_·⋆_/_ {B = B} L M refl) = conv⊢
  refl
  (sym (sub[]Nf' σ⋆ M B))
  (sub σ⋆ σ L ·⋆ subNf σ⋆ M / refl)
sub σ⋆ σ (wrap A B M) = wrap
  (subNf σ⋆ A)
  (subNf σ⋆ B)
  (conv⊢ refl (sub-nf-μ σ⋆ A B) (sub σ⋆ σ M))
sub σ⋆ σ (unwrap {A = A}{B} M refl) = conv⊢
  refl
  (sym (sub-nf-μ σ⋆ A B))
  (unwrap (sub σ⋆ σ M) refl)
sub σ⋆ σ (con {A} c refl) = con c (subNf∅-subNf σ⋆ A)
sub σ⋆ σ (builtin b / refl) = conv⊢ refl (btype-sub b σ⋆) (builtin b / refl)
sub σ⋆ σ (error A) = error (subNf σ⋆ A)
sub σ⋆ σ (constr e A refl x) = constr e _ refl (sub-VecList σ⋆ σ e A x)
sub σ⋆ σ (case x cs)  = case (sub  σ⋆ σ x) (sub-Cases σ⋆ σ cs)
\end{code}

\begin{code}
subcons : ∀{Φ Ψ Γ Δ}
  → (σ⋆ : SubNf Φ Ψ)
  → (σ : Sub σ⋆ Γ Δ)
  → {A : Φ ⊢Nf⋆ *}
  → (t : Δ ⊢ subNf σ⋆ A)
    ---------------------
  → (∀ {B : Φ ⊢Nf⋆ *} → Γ , A ∋ B → Δ ⊢ subNf σ⋆ B)
subcons σ⋆ σ t Z     = t
subcons σ⋆ σ t (S x) = σ x
\end{code}

\begin{code}
_[_] : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}
  → Γ , B ⊢ A
  → Γ ⊢ B 
    -----
  → Γ ⊢ A
_[_] {A = A}{B} b a = conv⊢ refl
  (subNf-id A)
  (sub ( ne ∘ `)
         (subcons (ne ∘ `)
                    (conv⊢ refl (sym (subNf-id _)) ∘ `)
                    (conv⊢ refl (sym (subNf-id B)) a))
         b)
\end{code}

\begin{code}
lem : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢Nf⋆ *}{A : Φ ⊢Nf⋆ K} → (x : Γ ,⋆ K ∋ B) → 
  Γ ⊢ subNf (subNf-cons (λ x₁ → ne (` x₁)) A) B
lem (T x) = conv⊢
  refl
  (weakenNf[] _ _)
  (` x)

_[_]⋆ : ∀ {Φ Γ K} {B : Φ ,⋆ K ⊢Nf⋆ *}
        → Γ ,⋆ K ⊢ B
        → (A : Φ ⊢Nf⋆ K)
          ---------
        → Γ ⊢ B [ A ]Nf
_[_]⋆ b A = sub
  (subNf-cons (ne ∘ `) A)
  lem
  b
\end{code}

# simply typed renaming

These are easier to reason about and show up in the CEK machine as
discharge is simply typed. Fully general rens/subs reasoning easily
gets bogged down with type coercions.

Note: This doesn't scale to substitution as we need to weaken by a
type var to go under a Λ.

\begin{code}
Renˢ : ∀{Φ} → Ctx Φ → Ctx Φ → Set
Renˢ Γ Δ = ∀{A} → Γ ∋ A → Δ ∋ A

extˢ : ∀ {Φ Γ Δ}
  → (ρ : Renˢ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
    -------------------------------
  → Renˢ (Γ , B) (Δ , B)
extˢ ρ Z     = Z
extˢ ρ (S x) = S (ρ x)

-- here we are manipulating the type contexts of the renaming but only
-- by extending them with the same kind
extˢ⋆ : ∀{Φ}{Γ Δ : Ctx Φ}
  → (ρ : Renˢ Γ Δ)
  → ∀ {K}
    ----------------------
  → Renˢ (Γ ,⋆ K) (Δ ,⋆ K)
extˢ⋆ ρ (T x) = T (ρ x)

renˢ : ∀ {Φ Γ Δ}
  → (ρ : Renˢ Γ Δ)
  → {A : Φ ⊢Nf⋆ *}
  → Γ ⊢ A
    -----
  → Δ ⊢ A

renˢ-List : ∀ {Φ Γ Δ}
  → (ρ : Renˢ Γ Δ)
  → {AS : List (Φ ⊢Nf⋆ *)}
  → ConstrArgs Γ AS
    ----------------------
  → ConstrArgs Δ AS
renˢ-List ρ [] = []
renˢ-List ρ (x ∷ xs) = renˢ ρ x ∷ (renˢ-List ρ xs)  

renˢ-ConstrArgs : ∀ {Φ Γ Δ n}
  → (ρ : Renˢ Γ Δ)
  → (e : Fin n)
  → (A : Vec (List (Φ ⊢Nf⋆ *)) n)
  → (xs : ConstrArgs Γ (lookup A e))
    -----
  → ConstrArgs Δ (lookup A e)
renˢ-ConstrArgs ρ zero (AS ∷ ASS) xs = renˢ-List ρ xs
renˢ-ConstrArgs ρ (suc e) (AS ∷ ASS) xs = renˢ-ConstrArgs ρ e ASS xs

renˢ-Cases : ∀ {Φ Γ Δ n}
  → (ρ : Renˢ Γ Δ) 
  → {A : Φ ⊢Nf⋆ *} 
  → {tss : Vec (List (Φ ⊢Nf⋆ *)) n} 
  → (cs : Cases Γ A tss)
    ------------------------------
  → Cases Δ A tss
renˢ-Cases ρ [] = []
renˢ-Cases ρ (c ∷ cs) = renˢ ρ c ∷ (renˢ-Cases ρ cs)

renˢ ρ (` x)           = ` (ρ x)
renˢ ρ (ƛ M)           = ƛ (renˢ (extˢ ρ) M)
renˢ ρ (L · M)         = renˢ ρ L · renˢ ρ M
renˢ ρ (Λ M)           = Λ (renˢ (extˢ⋆ ρ) M)
renˢ ρ (M ·⋆ A / p)    = renˢ ρ M ·⋆ A / p
renˢ ρ (wrap A B M)    = wrap A B (renˢ ρ M)
renˢ ρ (unwrap M p)    = unwrap (renˢ ρ M) p
renˢ ρ (con c refl)    = con c refl
renˢ ρ (builtin b / p) = builtin b / p
renˢ ρ (error _)       = error _
renˢ ρ (constr e A refl x)  = constr e A refl (renˢ-ConstrArgs ρ e A x)
renˢ ρ (case x cs)     = case (renˢ ρ x) (renˢ-Cases ρ cs)

weakenˢ : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}{B : Φ ⊢Nf⋆ *}
  → Γ ⊢ A
    ---------
  → Γ , B ⊢ A
weakenˢ M = renˢ S M

-- cannot define this using renˢ
{-
weaken⋆ˢ : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}{K}
  → Γ ⊢ A
    ------------------
  → Γ ,⋆ K ⊢ weakenNf A
-}

extˢ-id : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}(x : Γ , A ∋ B)
  → extˢ id x ≡ x
extˢ-id Z     = refl
extˢ-id (S x) = refl

extˢ-comp : ∀ {Φ Γ Δ Θ}{A B : Φ ⊢Nf⋆ *}
  → {ρ : Renˢ Δ Θ}{ρ' : Renˢ Γ Δ}(x : Γ , B ∋ A)
  → extˢ (ρ ∘ ρ') x ≡ extˢ ρ (extˢ ρ' x)
extˢ-comp Z     = refl
extˢ-comp (S x) = refl

extˢ⋆-id : ∀ {Φ Γ}{K}{A : Φ ,⋆ K ⊢Nf⋆ *}(x : Γ ,⋆ K ∋ A)
  → extˢ⋆ id x ≡ x
extˢ⋆-id (T x) = refl

extˢ⋆-comp : ∀ {Φ Γ Δ Θ}{K}{A : Φ ,⋆ K ⊢Nf⋆ *}
  → {ρ : Renˢ Δ Θ}{ρ' : Renˢ Γ Δ}(x : Γ ,⋆ K ∋ A)
  → extˢ⋆ (ρ ∘ ρ') x ≡ extˢ⋆ ρ (extˢ⋆ ρ' x)
extˢ⋆-comp (T x) = refl

extˢ-cong : ∀{Φ}{Γ Δ : Ctx Φ}{ρ ρ' : Renˢ Γ Δ}
          → (∀{A}(x : Γ ∋ A) → ρ x ≡ ρ' x)
          → ∀{A B}(x : Γ , A ∋ B)
            --------------------------------
          → extˢ ρ x ≡ extˢ ρ' x
extˢ-cong p Z = refl
extˢ-cong p (S x) = cong S (p x)

extˢ⋆-cong : ∀{Φ}{Γ Δ : Ctx Φ}{ρ ρ' : Renˢ Γ Δ}
          → (∀{A}(x : Γ ∋ A) → ρ x ≡ ρ' x)
          → ∀{K B}(x : Γ ,⋆ K ∋ B)
            --------------------------------
          → extˢ⋆ ρ x ≡ extˢ⋆ ρ' x
extˢ⋆-cong p (T x) = cong T (p x)

renˢ-cong : ∀{Φ}{Γ Δ : Ctx Φ}{ρ ρ' : Renˢ Γ Δ}
          → (∀{A}(x : Γ ∋ A) → ρ x ≡ ρ' x)
          → ∀{A}(M : Γ ⊢ A)
            --------------------------------
          → renˢ ρ M ≡ renˢ ρ' M

renˢ-List-cong : ∀{Φ}{Γ Δ : Ctx Φ}{ρ ρ' : Renˢ Γ Δ}
          → (∀{A}(x : Γ ∋ A) → ρ x ≡ ρ' x)
          → {AS : List (Φ ⊢Nf⋆ *)}
          → (cs : ConstrArgs Γ AS)
            --------------------------------
          → renˢ-List ρ cs ≡ renˢ-List ρ' cs
renˢ-List-cong p [] = refl
renˢ-List-cong p (t ∷ cs) = cong₂ _∷_ (renˢ-cong p t) (renˢ-List-cong p cs)

renˢ-ConstrArgs-cong : ∀{Φ}{Γ Δ : Ctx Φ}{ρ ρ' : Renˢ Γ Δ}{n}
          → (∀{A}(x : Γ ∋ A) → ρ x ≡ ρ' x)
          → (e : Fin n)
          → (A : Vec (List (Φ ⊢Nf⋆ *)) n)
          → (cs : ConstrArgs Γ (lookup A e))
            ---------------------------------------------------
          → renˢ-ConstrArgs ρ e A cs ≡ renˢ-ConstrArgs ρ' e A cs
renˢ-ConstrArgs-cong p zero (x ∷ A) cs = renˢ-List-cong p cs
renˢ-ConstrArgs-cong p (suc e) (x ∷ A) cs = renˢ-ConstrArgs-cong p e A cs

renˢ-Cases-cong : ∀ {Φ} {Γ Δ : Ctx Φ} {ρ ρ' : Renˢ Γ Δ}
                    (p : {A : Φ ⊢Nf⋆ *} (x : Γ ∋ A) → ρ x ≡ ρ' x)
                    {A : Φ ⊢Nf⋆ *} {n}
                    {tss : Vec (List (Φ ⊢Nf⋆ *)) n}
                    (cs : Cases Γ A tss)
                   --------------------------------------------------  
                 → renˢ-Cases ρ cs ≡ renˢ-Cases ρ' cs
renˢ-Cases-cong p [] = refl
renˢ-Cases-cong p (c ∷ cs) = cong₂ _∷_ (renˢ-cong p c) (renˢ-Cases-cong p cs)

renˢ-cong p (` x)           = cong ` (p x)
renˢ-cong p (ƛ M)           = cong ƛ (renˢ-cong (extˢ-cong p) M)
renˢ-cong p (L · M)         = cong₂ _·_ (renˢ-cong p L) (renˢ-cong p M)
renˢ-cong p (Λ M)           = cong Λ (renˢ-cong (extˢ⋆-cong p) M)
renˢ-cong p (M ·⋆ A / q)    = cong (_·⋆ A / q) (renˢ-cong p M)
renˢ-cong p (wrap A B M)    = cong (wrap A B) (renˢ-cong p M)
renˢ-cong p (unwrap M q)    = cong (λ M → unwrap M q) (renˢ-cong p M)
renˢ-cong p (con c refl)    = refl
renˢ-cong p (builtin b / q) = refl
renˢ-cong p (error _)       = refl
renˢ-cong p (constr e A refl x)  = cong (constr e A refl) (renˢ-ConstrArgs-cong p e A x)
renˢ-cong p (case M cs)     = cong₂ case (renˢ-cong p M) (renˢ-Cases-cong p cs)

renˢ-id : ∀ {Φ Γ}{A : Φ ⊢Nf⋆ *}(M : Γ ⊢ A)
  → renˢ id M ≡ M

renˢ-List-id : ∀ {Φ} {Γ : Ctx Φ} {A : List (Φ ⊢Nf⋆ *)}
                 (cs : ConstrArgs Γ A) →
               renˢ-List id cs ≡ cs
renˢ-List-id [] = refl
renˢ-List-id (t ∷ cs) = cong₂ _∷_ (renˢ-id t) (renˢ-List-id cs)

renˢ-ConstrArgs-id : ∀ {Φ} {Γ : Ctx Φ} {n} 
                    (e : Fin n)
                    (A : Vec (List (Φ ⊢Nf⋆ *)) n)
                    (cs : ConstrArgs Γ (lookup A e))
                    -----------------------------
                  → renˢ-ConstrArgs id e A cs ≡ cs
renˢ-ConstrArgs-id zero (A ∷ AS) cs = renˢ-List-id cs
renˢ-ConstrArgs-id (suc e) (A ∷ AS) cs = renˢ-ConstrArgs-id e AS cs

renˢ-Cases-id : ∀ {Φ} {Γ : Ctx Φ} {A : Φ ⊢Nf⋆ *} {n}
                  {tss : Vec (List (Φ ⊢Nf⋆ *)) n}
                  (cases : Cases Γ A tss) →
                renˢ-Cases id cases ≡ cases
renˢ-Cases-id [] = refl
renˢ-Cases-id (c ∷ cases) = cong₂ _∷_ (renˢ-id c) (renˢ-Cases-id cases)

renˢ-id (` x)               = refl
renˢ-id (ƛ M)               = cong ƛ (trans (renˢ-cong extˢ-id M) (renˢ-id M))
renˢ-id (L · M)             = cong₂ _·_ (renˢ-id L) (renˢ-id M)
renˢ-id (Λ M)               = cong Λ (trans (renˢ-cong extˢ⋆-id M) (renˢ-id M))
renˢ-id (M ·⋆ A / p)        = cong (_·⋆ A / p) (renˢ-id M)
renˢ-id (wrap A B M)        = cong (wrap A B) (renˢ-id M)
renˢ-id (unwrap M p)        = cong (λ M → unwrap M p) (renˢ-id M)
renˢ-id (con c refl)        = refl
renˢ-id (builtin b / p)     = refl
renˢ-id (error _)           = refl
renˢ-id (constr e A refl x) = cong (constr e A refl) (renˢ-ConstrArgs-id e A x)
renˢ-id (case M cases)      = cong₂ case (renˢ-id M) (renˢ-Cases-id cases)

renˢ-comp : ∀ {Φ Γ Δ Θ}{A : Φ ⊢Nf⋆ *}
  → {ρ : Renˢ Δ Θ}{ρ' : Renˢ Γ Δ}(M : Γ ⊢ A)
  → renˢ (ρ ∘ ρ') M ≡ renˢ ρ (renˢ ρ' M)

renˢ-List-comp : ∀ {Φ} {Γ Δ Θ : Ctx Φ} {ρ : Renˢ Δ Θ}
                   {ρ' : Renˢ Γ Δ} 
                   {A : List (Φ ⊢Nf⋆ *)}
                   (cs : ConstrArgs Γ A) 
            -------------------------------------------------
          → renˢ-List (ρ ∘ ρ') cs ≡ renˢ-List ρ (renˢ-List ρ' cs)
renˢ-List-comp [] = refl
renˢ-List-comp (t ∷ cs) = cong₂ _∷_ (renˢ-comp t) (renˢ-List-comp cs)

renˢ-ConstrArgs-comp : ∀ {Φ} {Γ Δ Θ : Ctx Φ} {ρ : Renˢ Δ Θ}
                         {ρ' : Renˢ Γ Δ} {n} 
                         (e : Fin n)
                         (A : Vec (List (Φ ⊢Nf⋆ *)) n)
                         (x : ConstrArgs Γ (lookup A e))
               --------------------------------------------------------------------------------
             → renˢ-ConstrArgs (ρ ∘ ρ') e A x ≡ renˢ-ConstrArgs ρ e A (renˢ-ConstrArgs ρ' e A x)
renˢ-ConstrArgs-comp zero (A ∷ AS) x = renˢ-List-comp x
renˢ-ConstrArgs-comp (suc e) (A ∷ AS) x = renˢ-ConstrArgs-comp e AS x

renˢ-Cases-comp : ∀ {Φ} {Γ Δ Θ : Ctx Φ} {A : Φ ⊢Nf⋆ *}
              {ρ : Renˢ Δ Θ} {ρ' : Renˢ Γ Δ} {n} {tss : Vec (List (Φ ⊢Nf⋆ *)) n}
              (cs : Cases Γ A tss)
              -------------------------------------------------------       
           →  renˢ-Cases (ρ ∘ ρ') cs ≡ renˢ-Cases ρ (renˢ-Cases ρ' cs)
renˢ-Cases-comp [] = refl
renˢ-Cases-comp (c ∷ cs) = cong₂ _∷_ (renˢ-comp c) (renˢ-Cases-comp cs)

renˢ-comp (` x)           = refl
renˢ-comp (ƛ M)           = cong ƛ (trans (renˢ-cong extˢ-comp M) (renˢ-comp M))
renˢ-comp (L · M)         = cong₂ _·_ (renˢ-comp L) (renˢ-comp M)
renˢ-comp (Λ M)           = cong Λ (trans (renˢ-cong extˢ⋆-comp M) (renˢ-comp M))
renˢ-comp (M ·⋆ A / p)    = cong (_·⋆ A / p) (renˢ-comp M)
renˢ-comp (wrap A B M)    = cong (wrap A B) (renˢ-comp M)
renˢ-comp (unwrap M p)    = cong (λ M → unwrap M p) (renˢ-comp M)
renˢ-comp (con c refl)    = refl
renˢ-comp (builtin b / p) = refl
renˢ-comp (error _)       = refl
renˢ-comp (constr e A refl x)  = cong (constr e A refl) (renˢ-ConstrArgs-comp e A x)
renˢ-comp (case M cs)     = cong₂ case (renˢ-comp M) (renˢ-Cases-comp cs)


Subˢ : ∀{Φ} → Ctx Φ → Ctx Φ → Set
Subˢ Γ Δ = ∀{A} → Γ ∋ A → Δ ⊢ A

extsˢ : ∀ {Φ Γ Δ}
  → (σ : Subˢ Γ Δ)
  → {B : Φ ⊢Nf⋆ *}
    ---------------------------------
  → Subˢ (Γ , B) (Δ , B)
extsˢ σ Z     = ` Z
extsˢ σ (S α) = weakenˢ (σ α)

-- cannot define this using renˢ
{-
exts⋆ˢ : ∀{Φ}{Γ Δ : Ctx Φ}
  → (σ : Subˢ Γ Δ)
  → ∀ {K}
    ----------------------
  → Subˢ (Γ ,⋆ K) (Δ ,⋆ K)
-}
\end{code}

   