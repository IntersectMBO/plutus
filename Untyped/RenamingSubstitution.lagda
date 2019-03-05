\begin{code}
module Untyped.RenamingSubstitution where
\end{code}

\begin{code}
open import Untyped.Term

open import Data.Nat
open import Data.Fin
open import Data.List
\end{code}

\begin{code}
Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

ext : ∀{m n} → Ren m n → Ren (suc m) (suc n)
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

ren     : ∀{m n} → Ren m n → m ⊢ → n ⊢
renList : ∀{m n} → Ren m n → List (m ⊢) → List (n ⊢)

ren ρ (` x)        = ` (ρ x)
ren ρ (ƛ t)        = ƛ (ren (ext ρ) t)
ren ρ (t · u)      = ren ρ t · ren ρ u
ren ρ (con tcn)    = con tcn
ren ρ (builtin ts) = builtin (renList ρ ts)
ren ρ error        = error

renList ρ []       = []
renList ρ (t ∷ ts) = ren ρ t ∷ renList ρ ts

Sub : ℕ → ℕ → Set
Sub m n = Fin m → n ⊢

exts : ∀{m n} → Sub m n → Sub (suc m) (suc n)
exts ρ zero = ` zero
exts ρ (suc x) = ren suc (ρ x)

sub     : ∀{m n} → Sub m n → m ⊢ → n ⊢
subList : ∀{m n} → Sub m n → List (m ⊢) → List (n ⊢)

sub σ (` x)        = σ x
sub σ (ƛ t)        = ƛ (sub (exts σ) t) 
sub σ (t · u)      = sub σ t · sub σ u
sub σ (con tcn)    = con tcn
sub σ (builtin ts) = builtin (subList σ ts)
sub σ error        = error

subList σ []       = []
subList σ (t ∷ ts) = sub σ t ∷ subList σ ts

extend : ∀{m n} → Sub m n → n ⊢ → Sub (suc m) n
extend σ t zero    = t
extend σ t (suc x) = σ x

_[_] : ∀{n} → suc n ⊢ → n ⊢ → n ⊢
t [ u ] = sub (extend ` u) t
\end{code}
