\begin{code}
module Scoped.Extrication where
\end{code}

\begin{code}
open import Data.Unit using (tt)
open import Data.Fin using (Fin;zero;suc;toℕ)
open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Properties using (+-comm)
open import Data.List using (List;[];_∷_)
open import Data.Vec using (Vec;[];_∷_;_++_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (refl;subst)

open import Utils as U using (Kind;*)
open import Utils.List using ([];_∷_)

open import RawU using (TmCon;tmCon;TyTag)
open import Builtin.Signature using (_⊢♯) 
open import Builtin.Constant.Type

open import Type using (Ctx⋆;∅;_,⋆_;_∋⋆_;Z;S)
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Algorithmic as A using (Ctx;_∋_;_⊢_;ConstrArgs;[];_∷_;Cases)
open Ctx
open _⊢_
open _∋_
open import Scoped using (ScopedTy;ScopedTm;Weirdℕ;WeirdFin)
open ScopedTy
open ScopedTm
open Weirdℕ
open WeirdFin
import Builtin.Constant.Type as T
import Builtin.Constant.Type as S
open import Algorithmic using (ty2sty;⟦_⟧;ty≅sty₁)
\end{code}

type level

\begin{code}
len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = zero
len⋆ (Γ ,⋆ K) = suc (len⋆ Γ)

extricateVar⋆ : ∀{Γ K}(A : Γ ∋⋆ K) → Fin (len⋆ Γ)
extricateVar⋆ Z     = zero
extricateVar⋆ (S α) = suc (extricateVar⋆ α)

extricateNf⋆ : ∀{Γ K}(A : Γ ⊢Nf⋆ K) → ScopedTy (len⋆ Γ)
extricateNe⋆ : ∀{Γ K}(A : Γ ⊢Ne⋆ K) → ScopedTy (len⋆ Γ)

extricateNf⋆-List :  ∀{Γ K}(AS : List (Γ ⊢Nf⋆ K)) → U.List (ScopedTy (len⋆ Γ))
extricateNf⋆-List [] = U.[]
extricateNf⋆-List (A ∷ AS) = extricateNf⋆ A U.∷ extricateNf⋆-List AS

extricateNf⋆-VecList :  ∀{Γ K n}(TSS : Vec (List (Γ ⊢Nf⋆ K)) n) → U.List (U.List (ScopedTy (len⋆ Γ)))
extricateNf⋆-VecList [] = U.[]
extricateNf⋆-VecList (TS ∷ TSS) = (extricateNf⋆-List TS) U.∷ (extricateNf⋆-VecList TSS)

-- intrinsically typed terms should also carry user chosen names as
-- instructions to the pretty printer

extricateNf⋆ (Π {K = K} A) = Π K (extricateNf⋆ A)
extricateNf⋆ (A ⇒ B)       = extricateNf⋆ A ⇒ extricateNf⋆ B
extricateNf⋆ (ƛ {K = K} A) = ƛ K (extricateNf⋆ A)
extricateNf⋆ (ne n)        = extricateNe⋆ n
extricateNf⋆ (con (ne x))  = extricateNe⋆ x
extricateNf⋆ (μ A B)       = μ (extricateNf⋆ A) (extricateNf⋆ B)
extricateNf⋆ (SOP x)       = SOP (extricateNf⋆-VecList x)

extricateNe⋆ (` α)    = ` (extricateVar⋆ α)
extricateNe⋆ (n · n') = extricateNe⋆ n · extricateNf⋆ n'
extricateNe⋆ (^ tc)   = con tc
\end{code}


\begin{code}
len : ∀{Φ} → Ctx Φ → Weirdℕ (len⋆ Φ)
len ∅        = Z
len (Γ ,⋆ K) = T (len Γ)
len (Γ , A)  = S (len Γ)



extricateVar : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ∋ A → WeirdFin (len Γ)
extricateVar Z     = Z
extricateVar (S x) = S (extricateVar x)
extricateVar (T x) = T (extricateVar x)

extricateSub : ∀ {Γ Δ} → (∀ {J} → Δ ∋⋆ J → Γ ⊢Nf⋆ J)
             → Scoped.Tel⋆ (len⋆ Γ) (len⋆ Δ)
extricateSub {Δ = ∅}     σ = []
extricateSub {Γ}{Δ ,⋆ K} σ =
  Eq.subst (Scoped.Tel⋆ (len⋆ Γ))
           (+-comm (len⋆ Δ) 1)
           (extricateSub {Δ = Δ} (σ ∘ S) ++ Data.Vec.[ extricateNf⋆ (σ Z) ])


extricate : ∀{Φ Γ}{A : Φ ⊢Nf⋆ *} → Γ ⊢ A → ScopedTm (len Γ)

extricate-ConstrArgs : ∀{Φ Γ}{AS : List (Φ ⊢Nf⋆ *)} → ConstrArgs Γ AS → U.List (ScopedTm (len Γ))
extricate-ConstrArgs [] = U.[]
extricate-ConstrArgs (c ∷ cs) = extricate c U.∷ extricate-ConstrArgs cs

extricate-Cases : ∀ {Φ} {Γ : Ctx Φ} {A : Φ ⊢Nf⋆ *} {n}
                 {tss : Vec (List (Φ ⊢Nf⋆ *)) n} 
                 (cases : Cases Γ A tss) 
                → U.List (ScopedTm (len Γ))
extricate-Cases [] = U.[]
extricate-Cases (c ∷ cs) = (extricate c) U.∷ (extricate-Cases cs)                

extricate (` x)                   = ` (extricateVar x)
extricate {Φ}{Γ} (ƛ {A = A} t)    = ƛ (extricateNf⋆ A) (extricate t)
extricate (t · u)                 = extricate t · extricate u
extricate (Λ {K = K} t)           = Λ K (extricate t)
extricate {Φ}{Γ} (t ·⋆ A / refl)  = extricate t ScopedTm.·⋆ extricateNf⋆ A
extricate {Φ}{Γ} (wrap pat arg t) = wrap (extricateNf⋆ pat) (extricateNf⋆ arg) (extricate t)
extricate (unwrap t refl)         = unwrap (extricate t)
extricate (con {A = A} c p)       = con (tmCon (ty2sty A) (subst ⟦_⟧ (ty≅sty₁ A) c))
extricate (builtin b / refl)      = builtin b
extricate (constr e A refl x)     = constr (extricateNf⋆ (SOP A)) (toℕ e) (extricate-ConstrArgs x)
extricate (case {A = A} x cases)  = case (extricateNf⋆ A) (extricate x) (extricate-Cases cases)
extricate {Φ}{Γ} (error A)        = error (extricateNf⋆ A)
\end{code}
