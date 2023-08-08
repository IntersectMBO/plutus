\begin{code}
module Declarative.Examples.StdLib.ChurchNat where
\end{code}

\begin{code}
open import Data.Integer using (ℤ)
open import Relation.Binary.PropositionalEquality using (refl)

open import Utils using (Kind;*)
open import Type using (Ctx⋆;_⊢⋆_;Z)
open _⊢⋆_
open import Declarative using (Ctx;_⊢_;_∋_)
open Ctx
open _⊢_
open _∋_
open import Type.RenamingSubstitution using (sub∅)
open import Builtin using (addInteger)
open import Builtin.Constant.Type using (TyCon;aInteger)
open import Type.Equality using (_≡β_)
open _≡β_
open TyCon
\end{code}

\begin{code}
integer = atomic aInteger

-- all (r :: *). r -> (r -> r) -> r
N : ∀{Φ} → Φ ⊢⋆ *
N = Π (` Z ⇒ (` Z ⇒ ` Z) ⇒ ` Z)

-- /\(r :: *) -> \(z : r) (f : r -> r) -> z
Zero : ∅ ⊢ N
Zero = Λ (ƛ (ƛ (` (S Z))))

-- \(n : nat) -> /\(r :: *) -> \(z : r) (f : r -> r) -> f (n {r} z f)
Succ : ∅ ⊢ N ⇒ N
Succ = ƛ (Λ (ƛ (ƛ (` Z · ((` (S (S (T Z)))) ·⋆ (` Z) · (` (S Z)) · (` Z))))))

Iter : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ Π (` Z ⇒ (` Z ⇒ ` Z) ⇒ N ⇒ (` Z))
Iter = Λ (ƛ (ƛ (ƛ ((` Z) ·⋆ (` Z) · (` (S (S Z))) · (` (S Z))))))

con0 : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con (^ integer)
con0 = con {A = ^ integer}(ℤ.pos 0) (refl≡β (^ (atomic aInteger))) 

con1 : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con (^ integer)
con1 = con {A = ^ integer}(ℤ.pos 1) (refl≡β (^ (atomic aInteger))) 

inc : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ con (^ integer) ⇒ con (^ integer)
inc = ƛ (builtin addInteger · con1  · ` Z)

Nat2Int : ∅ ⊢ N ⇒ con (^ integer)
Nat2Int = ƛ (Iter
  ·⋆ con (^ integer)
  ·  con0
  ·  inc
  ·  ` Z)
\end{code}
