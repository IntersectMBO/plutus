\begin{code}
module Scoped.Erasure.RenamingSubstitution where
\end{code}

\begin{code}
open import Untyped
import Untyped.RenamingSubstitution as U
open import Scoped
open import Scoped.Erasure
import Scoped.RenamingSubstitution as S

open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Data.List
\end{code}

\begin{code}
backVar : ∀{n}{w : Weirdℕ n} → Fin (len w) → WeirdFin w
backVar {w = S w} zero    = Z
backVar {w = S w} (suc i) = S (backVar i)
backVar {w = T w} i       = T (backVar i)

backVar-eraseVar : ∀{n}{w : Weirdℕ n}(i : WeirdFin w)
  → backVar (eraseVar i) ≡ i
backVar-eraseVar Z = refl
backVar-eraseVar (S i) = cong S (backVar-eraseVar i)
backVar-eraseVar (T i) = cong T (backVar-eraseVar i)

eraseVar-backVar : ∀{n}{w : Weirdℕ n}(i : Fin (len w))
  → eraseVar (backVar {n}{w} i) ≡ i
eraseVar-backVar {w = S w} zero    = refl
eraseVar-backVar {w = S w} (suc i) = cong suc (eraseVar-backVar {w = w} i)
eraseVar-backVar {w = T w} i       = eraseVar-backVar {w = w} i



erase-Ren : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}
  → S.Ren w w' → U.Ren (len w) (len w')
erase-Ren ρ i = eraseVar (ρ (backVar i))

lift-erase : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}
 → (ρ : S.Ren w w')
 → (α : Fin (len (S w)))
 → U.lift (erase-Ren ρ) α ≡ erase-Ren (S.lift ρ) α
lift-erase ρ zero    = refl
lift-erase ρ (suc α) = refl


ren-erase : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}
  → (ρ⋆ : S.Ren⋆ n n')
  → (ρ : S.Ren w w')
  → (t : ScopedTm w)
  → U.ren (erase-Ren ρ) (eraseTm t) ≡ eraseTm (S.ren ρ⋆ ρ t)

ren-eraseList : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}
  → (ρ⋆ : S.Ren⋆ n n')
  → (ρ : S.Ren w w')
  → (ts  : List (ScopedTm w))
  → U.renList (erase-Ren ρ) (eraseList ts) ≡ eraseList (S.renL ρ⋆ ρ ts)
ren-eraseList ρ⋆ ρ [] = refl
ren-eraseList ρ⋆ ρ (t ∷ ts) =
 cong₂ _∷_ (ren-erase ρ⋆ ρ t) (ren-eraseList ρ⋆ ρ ts)

ren-erase ρ⋆ ρ (` x)              =
  cong (` ∘ eraseVar ∘ ρ) (backVar-eraseVar x) 
ren-erase ρ⋆ ρ (Λ x K t)          = ren-erase (S.lift⋆ ρ⋆) (S.⋆lift ρ) t
ren-erase ρ⋆ ρ (t ·⋆ A)           = ren-erase ρ⋆ ρ t
ren-erase ρ⋆ ρ (ƛ x A t)          = cong
  (ƛ x)
  (trans (U.ren-cong (lift-erase ρ) (eraseTm t)) (ren-erase ρ⋆ (S.lift ρ) t))
ren-erase ρ⋆ ρ (t · u)            =
  cong₂ _·_ (ren-erase ρ⋆ ρ t) (ren-erase ρ⋆ ρ u)
ren-erase ρ⋆ ρ (con x)            = refl
ren-erase ρ⋆ ρ (error x)          = refl
ren-erase ρ⋆ ρ (builtin bn As ts) = cong (builtin bn) (ren-eraseList ρ⋆ ρ ts)
ren-erase ρ⋆ ρ (wrap pat ar t)    = ren-erase ρ⋆ ρ t
ren-erase ρ⋆ ρ (unwrap t)         = ren-erase ρ⋆ ρ t

--

erase-Sub : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}
  → S.Sub w w' → U.Sub (len w) (len w')
erase-Sub σ i = eraseTm (σ (backVar i))

slift-erase : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}
 → (σ : S.Sub w w')
 → (α : Fin (len (S w)))
 → U.lifts (erase-Sub σ) α ≡ erase-Sub (S.slift σ) α
slift-erase σ zero = refl
slift-erase {w' = w'} σ (suc α) = trans
  (U.ren-cong (cong suc ∘ sym ∘ eraseVar-backVar {w = w'})
              (eraseTm (σ (backVar α))))
  (ren-erase id S (σ (backVar α)))

⋆slift-erase : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}
 → (σ : S.Sub w w')
 → (α : Fin (len w))
 → erase-Sub σ α ≡ erase-Sub (S.⋆slift σ) α
⋆slift-erase {w' = w'} σ α = trans
  (trans (U.ren-id (eraseTm (σ (backVar α))))
         (U.ren-cong (sym ∘ eraseVar-backVar {w = w'})
                     (eraseTm (σ (backVar α)))))
  (ren-erase suc T (σ (backVar α)))

sub-erase : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}
  → (σ⋆ : S.Sub⋆ n n')
  → (σ : S.Sub w w')
  → (t : ScopedTm w)
  → U.sub (erase-Sub σ) (eraseTm t) ≡ eraseTm (S.sub σ⋆ σ t)

subList-erase : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}
  → (σ⋆ : S.Sub⋆ n n')
  → (σ : S.Sub w w')
  → (ts : List (ScopedTm w))
  → U.subList (erase-Sub σ) (eraseList ts) ≡ eraseList (S.subL σ⋆ σ ts)
subList-erase σ⋆ σ []       = refl
subList-erase σ⋆ σ (t ∷ ts) =
  cong₂ _∷_ (sub-erase σ⋆ σ t) (subList-erase σ⋆ σ ts)

sub-erase σ⋆ σ (` x) = cong (eraseTm ∘ σ) (backVar-eraseVar x)
sub-erase σ⋆ σ (Λ x K t)          = trans
  (U.sub-cong (⋆slift-erase σ) (eraseTm t))
  (sub-erase (S.slift⋆ σ⋆) (S.⋆slift σ) t)
sub-erase σ⋆ σ (t ·⋆ A)           = sub-erase σ⋆ σ t
sub-erase σ⋆ σ (ƛ x A t)          = cong
  (ƛ x)
  (trans (U.sub-cong (slift-erase σ) (eraseTm t))
         (sub-erase σ⋆ (S.slift σ) t))
sub-erase σ⋆ σ (t · u)            =
  cong₂ _·_ (sub-erase σ⋆ σ t) (sub-erase σ⋆ σ u)
sub-erase σ⋆ σ (con c)            = refl
sub-erase σ⋆ σ (error A)          = refl
sub-erase σ⋆ σ (builtin bn As ts) = cong
  (builtin bn)
  (subList-erase σ⋆ σ ts)
sub-erase σ⋆ σ (wrap pat arg t)   = sub-erase σ⋆ σ t
sub-erase σ⋆ σ (unwrap t)         = sub-erase σ⋆ σ t

erase-extend : ∀{n}{w : Weirdℕ n}
  → (u : ScopedTm w)
  → (α : Fin (suc (len w)))
  → erase-Sub (S.ext ` u) α ≡ U.extend ` (eraseTm u) α 
erase-extend u zero = refl
erase-extend {w = w} u (suc α) = cong ` (eraseVar-backVar {w = w} α)

lem[] : ∀{n}{w : Weirdℕ n}(t : ScopedTm (S w))(u : ScopedTm w) →
  eraseTm (t S.[ u ]) ≡ eraseTm t U.[ eraseTm u ]
lem[] t u = trans
  (sym (sub-erase ` (S.ext ` u) t))
       (U.sub-cong (erase-extend u) (eraseTm t))

lem[]⋆ : ∀{n}{w : Weirdℕ n}(t : ScopedTm (T w))(A : ScopedTy n) →
  eraseTm (t S.[ A ]⋆) ≡ eraseTm t
lem[]⋆ {w = w} t A = trans
  (sym (sub-erase (S.ext⋆ ` A) (S.⋆ext `) t))
  (trans (U.sub-cong (cong ` ∘ eraseVar-backVar {w = w})
                     (eraseTm t))
         (sym (U.sub-id (eraseTm t))))
\end{code}
