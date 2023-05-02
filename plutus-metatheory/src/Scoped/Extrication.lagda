\begin{code}
module Scoped.Extrication where
\end{code}

\begin{code}
open import Data.Unit using (tt)
open import Data.Fin using (Fin;zero;suc)
open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Properties using (+-comm)
open import Data.Vec using ([];_++_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (refl)

open import Utils using (Kind;*)

open import RawU using (TmCon;tmCon;TyTag)
open import Builtin.Signature using (_⊢♯;con) 
open import Builtin.Constant.Type ℕ (_⊢♯)

open import Type using (Ctx⋆;∅;_,⋆_;_∋⋆_;Z;S)
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Algorithmic as A using (Ctx;_∋_;_⊢_)
open Ctx
open _⊢_
open _∋_
open import Scoped using (ScopedTy;ScopedTm;Weirdℕ;WeirdFin)
open ScopedTy
open ScopedTm
open Weirdℕ
open WeirdFin
import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) as T
import Builtin.Constant.Type ℕ ScopedTy as S

open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as B using (TermCon)
open B.TermCon
\end{code}

type level

\begin{code}
len⋆ : Ctx⋆ → ℕ
len⋆ ∅ = zero
len⋆ (Γ ,⋆ K) = suc (len⋆ Γ)

extricateVar⋆ : ∀{Γ K}(A : Γ ∋⋆ K) → Fin (len⋆ Γ)
extricateVar⋆ Z     = zero
extricateVar⋆ (S α) = suc (extricateVar⋆ α)

extricateNf⋆ : ∀{Γ K}(A : Γ ⊢Nf⋆ K) → ScopedTy (len⋆ Γ)
extricateNe⋆ : ∀{Γ K}(A : Γ ⊢Ne⋆ K) → ScopedTy (len⋆ Γ)
extricateTyConNf⋆ : ∀{Γ}(A : T.TyCon Γ) → S.TyCon (len⋆ Γ)

-- intrinsically typed terms should also carry user chosen names as
-- instructions to the pretty printer

extricateTyConNf⋆ (T.list A) = S.list (extricateNf⋆ A)
extricateTyConNf⋆ (T.pair A B) = S.pair (extricateNf⋆ A) (extricateNf⋆ B) 
extricateTyConNf⋆ (T.atomic A) = S.atomic A

extricateNf⋆ (Π {K = K} A) = Π K (extricateNf⋆ A)
extricateNf⋆ (A ⇒ B) = extricateNf⋆ A ⇒ extricateNf⋆ B
extricateNf⋆ (ƛ {K = K} A) = ƛ K (extricateNf⋆ A)
extricateNf⋆ (ne n) = extricateNe⋆ n
extricateNf⋆ (con c) = con (extricateTyConNf⋆ c)
extricateNf⋆ (μ A B) = μ (extricateNf⋆ A) (extricateNf⋆ B)

extricateNe⋆ (` α) = ` (extricateVar⋆ α)
extricateNe⋆ (n · n') = extricateNe⋆ n · extricateNf⋆ n'
\end{code}


\begin{code}
len : ∀{Φ} → Ctx Φ → Weirdℕ (len⋆ Φ)
len ∅ = Z
len (Γ ,⋆ K) = T (len Γ)
len (Γ , A) = S (len Γ)



extricateVar : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ∋ A → WeirdFin (len Γ)
extricateVar Z = Z
extricateVar (S x) = S (extricateVar x)
extricateVar (T x) = T (extricateVar x)

extricateC : ∀{Γ}{A : Γ ⊢Nf⋆ *} → B.TermCon A → RawU.TmCon
extricateC (tmInteger i)    = tmCon (con integer) i
extricateC (tmBytestring b) = tmCon (con bytestring) b
extricateC (tmString s)     = tmCon (con string) s
extricateC (tmBool b)       = tmCon (con bool) b
extricateC tmUnit           = tmCon (con unit) tt
extricateC (tmData d)       = tmCon (con pdata) d
extricateC (tmBls12-381-g1-element e) = tmCon (con bls12-381-g1-element) e
extricateC (tmBls12-381-g2-element e) = tmCon (con bls12-381-g2-element) e
extricateC (tmBls12-381-mlresult r)   = tmCon (con bls12-381-mlresult) r

extricateSub : ∀ {Γ Δ} → (∀ {J} → Δ ∋⋆ J → Γ ⊢Nf⋆ J)
  → Scoped.Tel⋆ (len⋆ Γ) (len⋆ Δ)
extricateSub {Δ = ∅}     σ = []
extricateSub {Γ}{Δ ,⋆ K} σ =
  Eq.subst (Scoped.Tel⋆ (len⋆ Γ))
           (+-comm (len⋆ Δ) 1)
           (extricateSub {Δ = Δ} (σ ∘ S) ++ Data.Vec.[ extricateNf⋆ (σ Z) ])

extricate : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢ A → ScopedTm (len Γ)
extricate (` x) = ` (extricateVar x)
extricate {Φ}{Γ} (ƛ {A = A} t) = ƛ (extricateNf⋆ A) (extricate t)
extricate (t · u) = extricate t · extricate u
extricate (Λ {K = K} t) = Λ K (extricate t)
extricate {Φ}{Γ} (t ·⋆ A / refl) = extricate t ScopedTm.·⋆ extricateNf⋆ A
extricate {Φ}{Γ} (wrap pat arg t) = wrap (extricateNf⋆ pat) (extricateNf⋆ arg)
  (extricate t)
extricate (unwrap t refl) = unwrap (extricate t)
extricate (con c) = con (extricateC c)
extricate (builtin b / refl) = builtin b
extricate {Φ}{Γ} (error A) = error (extricateNf⋆ A)
\end{code}
