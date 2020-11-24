module Utils where

open import Data.Integer
open import Data.Bool
open import Data.Nat.Base as ℕ
  using (ℕ; z≤n; s≤s) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)

roleSign : ℤ → ℤ
roleSign x = x

pseudoLt : ℤ → ℤ → ℤ
pseudoLt (-[1+ m ]) (-[1+ n ]) = if (m ℕ.<ᵇ n) then (+ 0) else (+ 1)
pseudoLt (-[1+ m ]) (+    n)   = + 1
pseudoLt (+    m)   (-[1+ n ]) = + 0
pseudoLt (+    m)   (+    n )  = if (m ℕ.<ᵇ n) then (+ 1) else (+ 0)

max : ℤ → ℤ → ℤ
max a b = a ⊔ b