\begin{code}
{-# OPTIONS --rewriting #-}

module Scoped.Erasure where
\end{code}

\begin{code}
open import Scoped
open import Untyped
open import Untyped.RenamingSubstitution
open import Builtin
open import Utils

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Product
\end{code}

\begin{code}
len : ∀{n} → Weirdℕ n → ℕ
len Z     = 0
len (S i) = suc (len i)
len (T i) = len i
\end{code}

\begin{code}
eraseVar : ∀{n}{i : Weirdℕ n} → WeirdFin i → Fin (len i)
eraseVar Z     = zero
eraseVar (S x) = suc (eraseVar x)
eraseVar (T x) = eraseVar x

eraseTC : Scoped.TermCon → Untyped.TermCon
eraseTC (integer i)    = integer i
eraseTC (bytestring b) = bytestring b
eraseTC (string s)     = string s
eraseTC (bool b)       = bool b
eraseTC (char c)       = char c
eraseTC unit           = unit

eraseTm : ∀{n}{i : Weirdℕ n} → ScopedTm i → len i ⊢

{-
eraseTel⋆ : ∀{m n}(i : Weirdℕ n) → Vec (ScopedTy n) m → Vec (len i ⊢) m
eraseTel⋆ i []       = []
eraseTel⋆ i (A ∷ As) = plc_dummy ∷ eraseTel⋆ i As
-}
eraseTel : ∀{m n}{i : Weirdℕ n} → Vec (ScopedTm i) m → Vec (len i ⊢) m

eraseTel []       = []
eraseTel (t ∷ ts) = eraseTm t ∷ eraseTel ts

eraseTm (` x)                  = ` (eraseVar x)
eraseTm (Λ K t)                = delay (eraseTm t)
eraseTm (t ·⋆ A)               = force (eraseTm t)
eraseTm (ƛ A t)                = ƛ (eraseTm t)
eraseTm (t · u)                = eraseTm t · eraseTm u
eraseTm (con c)                = con (eraseTC c)
eraseTm (error A)              = error
eraseTm (wrap pat arg t)       = eraseTm t
eraseTm (unwrap t)             = eraseTm t
eraseTm (ibuiltin b)           = error -- builtin b (≤″⇒≤‴ (≤⇒≤″ z≤n)) []
\end{code}
