\begin{code}
module Declarative.Erasure where
\end{code}

\begin{code}
open import Declarative
open import Type.RenamingSubstitution as T
open import Untyped
open import Untyped.RenamingSubstitution as U
\end{code}

\begin{code}
open import Type
open import Declarative
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con
  renaming (TermCon to TyTermCon)
open import Data.Nat
open import Data.Fin
open import Data.List

len : ∀{Φ} → Ctx Φ → ℕ
len ∅        = 0
len (Γ ,⋆ K) = len Γ
len (Γ , A)  = suc (len Γ)

eraseVar : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ∋ A → Fin (len Γ)
eraseVar Z     = zero 
eraseVar (S α) = suc (eraseVar α) 
eraseVar (T α) = eraseVar α

eraseTC : ∀{Φ}{Γ : Ctx Φ}{A : Φ ⊢⋆ *} → TyTermCon A → TermCon
eraseTC (integer i)    = integer i
eraseTC (bytestring b) = bytestring b
eraseTC (string s)     = string s

eraseTel : ∀{Φ Γ Δ}{σ : T.Sub Δ Φ}{As : List (Δ ⊢⋆ *)}
  → Declarative.Tel Γ Δ σ As
  → Untyped.Tel (len Γ)
erase : ∀{Φ Γ}{A : Φ ⊢⋆ *} → Γ ⊢ A → len Γ ⊢

erase (` α)             = ` (eraseVar α)
erase (ƛ t)             = ƛ (erase t) 
erase (t · u)           = erase t · erase u
erase (Λ t)             = ƛ (U.weaken (erase t))
erase (t ·⋆ A)          = erase t · plc_dummy
erase (wrap1 pat arg t) = erase t
erase (unwrap1 t)       = erase t
erase (conv p t)        = erase t
erase {Φ}{Γ} (con t)    = con (eraseTC {Γ = Γ} t)
erase (builtin bn σ ts) = builtin bn (eraseTel ts)
erase (error A)         = error

open import Data.Product renaming (_,_ to _,,_)

eraseTel {As = []}     _          = []
eraseTel {As = x ∷ As} (t ,, tel) = erase t ∷ eraseTel tel
\end{code}
