\begin{code}
module Scoped.Erasure.RenamingSubstitution where
\end{code}

\begin{code}
open import Untyped
import Untyped.RenamingSubstitution as U
open import Scoped
open import Scoped.Erasure
import Scoped.RenamingSubstitution as S

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


erase-Ren : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}
  → S.Ren w w' → U.Ren (len w) (len w')
erase-Ren ρ i = eraseVar (ρ (backVar i))

lift-erase : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'}
 → (ρ : S.Ren w w')
 → (α : Fin (len (S w)))
 → U.ext (erase-Ren ρ) α ≡ erase-Ren (S.lift ρ) α
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

lem[] : ∀{n}{w : Weirdℕ n}(t : ScopedTm (S w))(u : ScopedTm w) →
  eraseTm (t S.[ u ]) ≡ eraseTm t U.[ eraseTm u ]
lem[] = {!!}

lem[]⋆ : ∀{n}{w : Weirdℕ n}(t : ScopedTm (T w))(A : ScopedTy n) →
  eraseTm (t S.[ A ]⋆) ≡ eraseTm t
lem[]⋆ = {!!}
\end{code}
