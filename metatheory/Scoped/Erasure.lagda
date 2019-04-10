\begin{code}
module Scoped.Erasure where
\end{code}

\begin{code}
open import Type
open import Type.BetaNormal
open import Algorithmic as A
open import Scoped
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢Nf⋆_ con size⋆
open import Data.Nat
open import Data.Fin
open import Type.BetaNormal
open import Type.RenamingSubstitution as T
\end{code}

\begin{code}
len : Ctx → Weirdℕ
len ∅ = Z
len (Γ ,⋆ K) = T (len Γ)
len (Γ , A) = S (len Γ)

len⋆ : Ctx⋆ → ℕ
len⋆ ∅ = zero
len⋆ (Γ ,⋆ K) = suc (len⋆ Γ)

-- scoped kind clearly shoud go...
eraseK : Kind → ScopedKind
eraseK * = *
eraseK # = #
eraseK (K ⇒ J) = eraseK K ⇒ eraseK J

eraseVar⋆ : ∀{Γ K}(A : Γ ∋⋆ K) → Fin (len⋆ Γ)
eraseVar⋆ Z     = zero
eraseVar⋆ (S α) = suc (eraseVar⋆ α)

eraseNf⋆ : ∀{Γ K}(A : Γ ⊢Nf⋆ K) → ScopedTy (len⋆ Γ)
eraseNe⋆ : ∀{Γ K}(A : Γ ⊢NeN⋆ K) → ScopedTy (len⋆ Γ)

-- intrinsically typed terms should also carry user chosen names as
-- instructions to the pretty printer

eraseNf⋆ (Π {K = K} A) = Π "x" (eraseK K) (eraseNf⋆ A)
eraseNf⋆ (A ⇒ B) = eraseNf⋆ A ⇒ eraseNf⋆ B
eraseNf⋆ (ƛ {K = K} A) = ƛ "x" (eraseK K) (eraseNf⋆ A)
eraseNf⋆ (ne n) = eraseNe⋆ n
eraseNf⋆ (size⋆ n) = size n
eraseNf⋆ (con c A) = con c

eraseNe⋆ (` α) = ` (eraseVar⋆ α)
eraseNe⋆ (n · n') = eraseNe⋆ n · eraseNf⋆ n'
-- ((K ⇒ *) ⇒ K ⇒ *) ⇒ K ⇒ *
eraseNe⋆ (μ1 {K = K}) = ƛ "x"
  ((eraseK K ⇒ *) ⇒ eraseK K ⇒ *)
  (ƛ "y" (eraseK K) (μ (` (suc zero)) (` zero)))

eraseVar : ∀{Γ K}{A : A.∥ Γ ∥ ⊢Nf⋆ K} → Γ ∋ A → WeirdFin (len Γ)
eraseVar Z = Z
eraseVar (S x) = S (eraseVar x)
eraseVar (T x) = T (eraseVar x)

open import Relation.Binary.PropositionalEquality as Eq
lem : ∀ Γ → Scoped.∥ len Γ ∥ ≡ len⋆ A.∥ Γ ∥
lem ∅ = refl
lem (Γ ,⋆ K) = cong suc (lem Γ)
lem (Γ , A) = lem Γ

eraseC : ∀{Γ}{A : Γ ⊢Nf⋆ *} → TermCon A → SizedTermCon
eraseC (integer s i p) = integer s i p
eraseC (bytestring s b p) = bytestring s b p
eraseC (size s) = size s

open import Data.List as L
open import Data.Product as P
open import Function hiding (_∋_)

eraseSub : ∀ {Γ Δ} → (∀ {J} → Δ ∋⋆ J → Γ ⊢Nf⋆ J) → List (ScopedTy (len⋆ Γ))
eraseSub {Δ = ∅} σ = []
eraseSub {Δ = Δ ,⋆ K} σ = eraseSub {Δ = Δ} (σ ∘ S) ++ L.[ eraseNf⋆ (σ Z) ]

eraseSub' : ∀ Γ {Δ} → (∀ {J} → Δ ∋⋆ J → A.∥ Γ ∥ ⊢Nf⋆ J)
  → List (ScopedTy (Scoped.∥ len Γ ∥))
eraseSub' Γ rewrite lem Γ = eraseSub

eraseTel : ∀ {Γ Δ}(σ : ∀ {J} → Δ ∋⋆ J → A.∥ Γ ∥ ⊢Nf⋆ J)(as : List (Δ ⊢Nf⋆ *)) → Tel Γ Δ σ as
  → List (ScopedTm (len Γ))
erase : ∀{Γ K}{A : A.∥ Γ ∥ ⊢Nf⋆ K} → Γ ⊢ A → ScopedTm (len Γ)

eraseTel σ [] x = []
eraseTel σ (A ∷ As) (t P., ts) = eraseTel σ As ts ++ L.[ erase t ]

erase (` x) = ` (eraseVar x)
erase {Γ} (ƛ {A = A} t) =
  ƛ "x" (Eq.subst ScopedTy (sym (lem Γ)) (eraseNf⋆ A) ) (erase t)
erase (t · u) = erase t · erase u
erase (Λ {K = K} t) = Λ "x" (eraseK K) (erase t)
erase {Γ} (t ·⋆ A) = erase t ·⋆ Eq.subst ScopedTy (sym (lem Γ)) (eraseNf⋆ A) 
erase {Γ} (wrap1 pat arg t) = wrap
  (Eq.subst ScopedTy (sym (lem Γ)) (eraseNf⋆ pat))
  (Eq.subst ScopedTy (sym (lem Γ)) (eraseNf⋆ arg))
  (erase t)
erase (unwrap1 t) = unwrap (erase t)
erase (con c) = con (eraseC c)
erase {Γ} (builtin b σ ts) = builtin b (eraseSub' Γ σ) (eraseTel σ _ ts)
erase {Γ} (error A) = error (Eq.subst ScopedTy (sym (lem Γ)) (eraseNf⋆ A) )
\end{code}

erasure commutes with renaming/substitution

\begin{code}
open import Algorithmic.RenamingSubstitution as AS
open import Scoped.RenamingSubstitution as SS

eraseRenNf⋆ : ∀{Γ Δ}(ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J) 
  → Ren⋆ (len⋆ Γ) (len⋆ Δ)
eraseRenNf⋆ {Γ ,⋆ K} ρ⋆ zero = eraseVar⋆ (ρ⋆ Z)
eraseRenNf⋆ {Γ ,⋆ K} ρ⋆ (suc α) = eraseRenNf⋆ (ρ⋆ ∘ S) α

eraseRen : ∀{Γ Δ}(ρ⋆ : ∀ {J} → A.∥ Γ ∥ ∋⋆ J → A.∥ Δ ∥ ∋⋆ J) →
  (ρ : ∀{J}{A : A.∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renameNf ρ⋆ A)
  → SS.Ren (len Γ) (len Δ)
eraseRen {Γ ,⋆ K} {Δ} ρ⋆ ρ (T x) = eraseRen
  (ρ⋆ ∘ S)
  (λ {_}{A} x → Eq.subst (Δ ∋_) (sym (renameNf-comp A)) (ρ (T x)))
  x
eraseRen {Γ A., A} ρ⋆ ρ Z = eraseVar (ρ Z)
eraseRen {Γ A., A} ρ⋆ ρ (S x) = eraseRen ρ⋆ (ρ ∘ S) x

ren-eraseVar⋆ : ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (α : Γ ∋⋆ J)
  → eraseRenNf⋆ ρ⋆ (eraseVar⋆ α) ≡ eraseVar⋆ (ρ⋆ α)
ren-eraseVar⋆ ρ⋆ Z     = refl
ren-eraseVar⋆ ρ⋆ (S α) = ren-eraseVar⋆ (ρ⋆ ∘ S) α

ren-eraseVar-T : ∀{Δ K}{A A' : A.∥ Δ ∥ ⊢Nf⋆ K}(p :  A ≡ A') → (x : Δ ∋ A) → 
  eraseVar (Eq.subst (Δ ∋_) p x)
  ≡
  eraseVar x
ren-eraseVar-T refl x = refl

ren-eraseVar : ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → A.∥ Γ ∥ ∋⋆ J → A.∥ Δ ∥ ∋⋆ J)
  → (ρ : ∀ {J} {A : A.∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renameNf ρ⋆ A)
  → {A : A.∥ Γ ∥ ⊢Nf⋆ J}
  → (x : Γ ∋ A)
  → eraseRen ρ⋆ ρ (eraseVar x) ≡ eraseVar (ρ x)
ren-eraseVar ρ⋆ ρ Z = refl
ren-eraseVar ρ⋆ ρ (S x) = ren-eraseVar ρ⋆ (ρ ∘ S) x 
ren-eraseVar {Γ ,⋆ K}{Δ} ρ⋆ ρ (T {A = A} x) = trans
  (ren-eraseVar
    (ρ⋆ ∘ S)
    (λ {_}{A} x → Eq.subst (Δ ∋_) (sym (renameNf-comp A)) (ρ (T x)))
    x)
  (ren-eraseVar-T (sym (renameNf-comp A)) (ρ (T x)))

eraseRenNf⋆-comp : ∀{B Γ Δ}(ρ⋆' : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)(ρ⋆ : ∀ {J} → B ∋⋆ J → Γ ∋⋆ J) → ∀ x → (eraseRenNf⋆ ρ⋆' ∘ eraseRenNf⋆ ρ⋆) x ≡ eraseRenNf⋆ (ρ⋆' ∘ ρ⋆) x
eraseRenNf⋆-comp {B ,⋆ K} ρ⋆' ρ⋆ zero = ren-eraseVar⋆ ρ⋆' (ρ⋆ Z)
eraseRenNf⋆-comp {B ,⋆ K} ρ⋆' ρ⋆ (suc x) = eraseRenNf⋆-comp ρ⋆' (ρ⋆ ∘ S) x  

-- I guess i could prove identity as well

-- here it starts to go south

lift⋆-erase⋆ : ∀{Γ Δ K}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (A : Fin (suc (len⋆ Γ)))
  → lift⋆ (eraseRenNf⋆ ρ⋆) A ≡ eraseRenNf⋆ {Γ ,⋆ K} {Δ ,⋆ K} (T.ext ρ⋆) A
lift⋆-erase⋆ ρ⋆ zero = refl
lift⋆-erase⋆ ρ⋆ (suc α) = ?

ren⋆-erase⋆ : ∀{Γ Δ K}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (A : Γ ⊢Nf⋆ K)
  → ren⋆ (eraseRenNf⋆ ρ⋆) (eraseNf⋆ A) ≡ eraseNf⋆ (renameNf ρ⋆ A)
ren⋆-erase⋆ ρ⋆ (Π A) = cong
  (Π "x" (eraseK _))
  (trans
    {!ren⋆-erase ρ⋆!} -- (ren⋆-cong {!!} (eraseNf⋆ A))
    (ren⋆-erase⋆ (T.ext ρ⋆) A))
ren⋆-erase⋆ ρ⋆ (A ⇒ B) = cong₂ _⇒_ (ren⋆-erase⋆ ρ⋆ A) (ren⋆-erase⋆ ρ⋆ B)
ren⋆-erase⋆ ρ⋆ (ƛ A) = cong
  (ƛ "x" (eraseK _))
  (trans
    {!!}
    (ren⋆-erase⋆ (T.ext ρ⋆) A))
ren⋆-erase⋆ ρ⋆ (ne x) = {!!}
ren⋆-erase⋆ ρ⋆ (size⋆ x) = {!!}
ren⋆-erase⋆ ρ⋆ (con x A) = {!!}

ren-eraseƛ₁ : ∀{Γ Δ Γ' Δ' K}
  → (ρ⋆ : ∀ {J} → A.∥ Γ ∥ ∋⋆ J → A.∥ Δ ∥ ∋⋆ J)
  → (A  : A.∥ Γ ∥ ⊢Nf⋆ K)
  → (p : len⋆ A.∥ Γ ∥ ≡ Γ')
  → (q : len⋆ A.∥ Δ ∥ ≡ Δ')
  → ren⋆ (subst₂ Ren⋆ p q (eraseRenNf⋆ ρ⋆))
    (Eq.subst ScopedTy p (eraseNf⋆ A)) 
    ≡ Eq.subst ScopedTy q (eraseNf⋆ (renameNf ρ⋆ A))
ren-eraseƛ₁ ρ⋆ A refl refl = {!!}

ren-erase : ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → A.∥ Γ ∥ ∋⋆ J → A.∥ Δ ∥ ∋⋆ J)
  → (ρ : ∀ {J} {A : A.∥ Γ ∥ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renameNf ρ⋆ A)
  → {A : A.∥ Γ ∥ ⊢Nf⋆ J}
  → (t : Γ ⊢ A)
  →  SS.ren
       (subst₂ Ren⋆ (sym (lem Γ)) (sym (lem Δ)) (eraseRenNf⋆ ρ⋆))
       (eraseRen ρ⋆ ρ)
       (erase t)
     ≡ erase (AS.rename ρ⋆ ρ t)


ren-erase ρ⋆ ρ (` x) = cong ` (ren-eraseVar ρ⋆ ρ x)
ren-erase ρ⋆ ρ (ƛ t) = cong₂ (ƛ "x") {!ren!} {!!} 
ren-erase ρ⋆ ρ (t · u) = cong₂ _·_ (ren-erase ρ⋆ ρ t) (ren-erase ρ⋆ ρ u)
ren-erase ρ⋆ ρ (Λ t) = cong (Λ "x" (eraseK _)) {!ren-erase (T.ext ρ⋆) (AS.ext⋆ ρ⋆ ρ) t!}
ren-erase ρ⋆ ρ (t ·⋆ A) = {!!}
ren-erase ρ⋆ ρ (wrap1 pat arg t) = {!!}
ren-erase ρ⋆ ρ (unwrap1 t) = {!!}
ren-erase ρ⋆ ρ (con x) = {!!}
ren-erase ρ⋆ ρ (builtin bn σ ts) = {!cong (builtin bn)!}
ren-erase {Γ}{Δ} ρ⋆ ρ (error A) = cong error {!!}

-- I need to use the same kind of techniques as the
-- soundness/completeness proofs for Declarative/Algorithmic

\end{code}

\begin{code}
-- a naturality/simulation proof about intrinscially vs extrinsically typed evaluation connected by erasure

open import Data.Sum
open import Algorithmic.Reduction as AR
open import Algorithmic.Evaluation as AE
open import Scoped.Reduction as SR
open import Utils

erase—→ : ∀{Γ K}{A : A.∥ Γ ∥ ⊢Nf⋆ K}{t t' : Γ ⊢ A} → t AR.—→ t' → erase t SR.—→ erase t'
eraseVal : ∀{Γ K}{A : A.∥ Γ ∥ ⊢Nf⋆ K}{t : Γ ⊢ A} → AR.Value t → SR.Value (erase t)
eraseE : ∀{Γ}{A : A.∥ Γ ∥ ⊢Nf⋆ *}{t : Γ ⊢ A} → AR.Error t → SR.Error (erase t)
eraseE E-error = E-error _
eraseE (E-·₁ p) = E-·₁ (eraseE p)
eraseE (E-·₂ p) = E-·₂ (eraseE p)
eraseE (E-·⋆ p) = E-·⋆ (eraseE p)
eraseE (E-unwrap p) = E-unwrap (eraseE p)
eraseE (E-builtin bn σ tel Bs Ds vtel x p tel') = E-builtin (eraseE x)

eraseVal V-ƛ = V-ƛ "x" _ _
eraseVal V-Λ_ = SR.V-Λ "x" _ _
eraseVal V-wrap1 = V-wrap _ _ _
eraseVal (V-con cn) = V-con (eraseC cn)

erase—→ (ξ-·₁ p)   = ξ-·₁ (erase—→ p)
erase—→ (ξ-·₂ p q) = ξ-·₂ (eraseVal p) (erase—→ q)
erase—→ (ξ-·⋆ p) = ξ-·⋆ (erase—→ p)
erase—→ (β-ƛ {N = N}{W = W} p) = {!SR.β-ƛ {x = "x"}{L = erase N}{M = erase W}!}
erase—→ {Γ}{K}{A} (β-Λ {N = N}{W = W}) = {!SR.β-Λ {x = "x"}{K = eraseK K}{L = erase N}{A = eraseNf⋆' Γ W}!}
erase—→ β-wrap1 = β-wrap
erase—→ (ξ-unwrap1 p) = ξ-unwrap (erase—→ p)
erase—→ (β-builtin bn σ tel vtel) = {!!}
erase—→ (ξ-builtin bn σ tel Bs Ds vtel p p' tel') = {!SR.ξ-builtin {b = bn} ? (erase—→ p) ?!}

{-
lemma : {A : ∅ ⊢Nf⋆ *}(t : ∅ ⊢ A) →
  (Σ (∅ ⊢ A) λ t' → Σ (t AR.—→ t') λ p → AR.progress t ≡ step p
    × SR.progress (erase t) ≡ inj₂ (erase t' P., {!!}))
  ⊎
  (Σ (AR.Value t) λ v → AR.progress t ≡ done v
    × SR.progress (erase t) ≡ inj₁ (inj₁ {!!}))
  ⊎
  Σ (AR.Error t) λ e → AR.progress t ≡ error e
    × SR.progress (erase t) ≡ inj₁ (inj₂ {!!})
lemma t = {!!}
-}
{-
theorem : {A : ∅ ⊢Nf⋆ *}(t : ∅ ⊢ A) → 
  -- for any n such that eval terminates with a value, then run also terminates with the erasure of the same value
  ∀ n → (p : Σ (∅ ⊢ A) λ t' → Σ (t AR.—↠ t') λ p → Σ (AR.Value t') λ v → eval (gas n) t ≡ steps p (done t' v))
  → proj₁ (run (erase t) n) ≡ erase (proj₁ p) × Σ (SR.Value (proj₁ (run (erase t) n))) λ v → proj₂ (proj₂ (run (erase t) n)) ≡ inj₁ (just v)
  -- question: is the last clause needed?
theorem t (suc n) (t' P., p P., v P., q) with AR.progress t | SR.progress (erase t)
theorem t (suc n) (t' P., p P., v P., q) | step x | inj₁ q' = {!!}
theorem t (suc n) (t' P., p P., v P., q) | step x | inj₂ y = {!!}
theorem t (suc n) (.t P., refl—↠ P., v P., q) | done v' | inj₁ (inj₁ v'') = refl P., (v'' P., refl)
theorem t (suc n) (.t P., refl—↠ P., v P., q) | done v' | inj₁ (inj₂ e) = refl P., {!!} -- missing info, I would need that something reduces to e...
theorem t (suc n) (t' P., p P., v P., q) | done x | inj₂ y = {!!}
-}
\end{code}
