```
module Check where
```

```
open import Scoped
open import Type
--open import Scoped.Extrication hiding (len;len⋆)
open import Declarative
open import Utils
open import Data.Nat
open import Data.Fin
```

```
len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = 0
len⋆ (Φ ,⋆ K) = suc (len⋆ Φ)

inferTyVar : ∀ Φ → Fin (len⋆ Φ) → Kind
inferTyVar (Φ ,⋆ K) zero    = K
inferTyVar (Φ ,⋆ _) (suc i) = inferTyVar Φ i

lookup' : ∀ Φ (i : Fin (len⋆ Φ)) → Φ ∋⋆ inferTyVar Φ i
lookup' (Φ ,⋆ K) zero    = Z
lookup' (Φ ,⋆ K) (suc i) = S (lookup' Φ i)

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>= f = f a
nothing >>= f = nothing

return : {A : Set} → A → Maybe A
return = just

open import Data.Bool
eqKind : Kind → Kind → Bool
eqKind * *       = Bool.true
eqKind * (_ ⇒ _) = Bool.false
eqKind (_ ⇒ _) * = Bool.false
eqKind (K ⇒ J) (K' ⇒ J') = eqKind K K' ∧ eqKind J J'

open import Relation.Nullary
open import Relation.Binary.Core using (Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_])
eqKind' : Decidable {A = Kind} _≡_
eqKind' * *       = yes refl
eqKind' * (_ ⇒ _) = no λ()
eqKind' (_ ⇒ _) * = no λ()
eqKind' (K ⇒ J) (K' ⇒ J') with eqKind' K K'
... | no  q = no (λ{refl → q refl})
... | yes p with eqKind' J J'
... | yes p' = yes (cong₂ _⇒_ p p')
... | no  q' = no (λ{refl → q' refl})

meqKind : (K K' : Kind) → Maybe (K ≡ K')
meqKind * *       = just refl 
meqKind * (_ ⇒ _) = nothing
meqKind (_ ⇒ _) * = nothing
meqKind (K ⇒ J) (K' ⇒ J') with meqKind K K'
... | nothing = nothing
... | just p with meqKind J J'
... | nothing = nothing
... | just q = just (cong₂ _⇒_ p q)

-- it doesn't seem to be possible to seperate inferring the kind and
-- and producing a typed term, so `inferKind` is here only as a warmup

inferKind : (Φ : Ctx⋆) → ScopedTy (len⋆ Φ) → Maybe Kind
inferKind Φ (` α)       = return (inferTyVar Φ α)
inferKind Φ (A ⇒ B)     = do
  * ← inferKind Φ A
    where _ → nothing
  * ← inferKind Φ B
    where _ → nothing
  return *
inferKind Φ (Π x K A)   = do
  * ← inferKind (Φ ,⋆ K) A
    where _ → nothing
  return * 
inferKind Φ (ƛ x K A)   = do
  J ← inferKind (Φ ,⋆ K) A
  return (K ⇒  J)
inferKind Φ (A · B)     = do
  K ⇒ J ← inferKind Φ A
    where _ → nothing
  K' ← inferKind Φ B
  if eqKind K K' then return J else nothing
inferKind Φ (con _)     = return *
inferKind Φ (μ pat arg) = do 
  (K ⇒ *) ⇒ K' ⇒ * ← inferKind Φ pat
    where _ → nothing
  K'' ← inferKind Φ arg
  if eqKind K K' ∧ eqKind K' K'' then return * else nothing

open import Data.Product renaming (_,_ to _,,_)
bondKind : (Φ : Ctx⋆)(A : ScopedTy (len⋆ Φ)) → Maybe (Σ Kind (Φ ⊢⋆_))
bondKind Φ (` α)   = return (inferTyVar Φ α ,, ` (lookup' Φ α))
bondKind Φ (A ⇒ B) = do
  * ,, A ← bondKind Φ A
    where _ → nothing
  * ,, B ← bondKind Φ B
    where _ → nothing
  return (* ,, A ⇒ B)
bondKind Φ (Π x K A) = do
  * ,, A ← bondKind (Φ ,⋆ K) A
    where _ → nothing
  return (* ,, Π x A)
bondKind Φ (ƛ x K A) = do
  J ,, A ← bondKind (Φ ,⋆ K) A
  return (K ⇒ J ,, ƛ x A)
bondKind Φ (A · B) = do
  K ⇒ J ,, A ← bondKind Φ A
    where _ → nothing
  K' ,, B ← bondKind Φ B
  refl ← meqKind K K'
  return (J ,, A · B)
bondKind Φ (con tc)     = just (* ,, con tc)
bondKind Φ (μ pat arg) = do
  (K ⇒ *) ⇒ K' ⇒ * ,, pat ← bondKind Φ pat
    where _ → nothing
  K'' ,, arg ← bondKind Φ arg
  refl ← meqKind K K'
  refl ← meqKind K' K''
  return (* ,, (μ1 · pat · arg))

len : ∀{Φ} → Ctx Φ → Weirdℕ (len⋆ Φ)
len ∅        = Z
len (Γ ,⋆ J) = Weirdℕ.T (len Γ)
len (Γ , A)  = Weirdℕ.S (len Γ)

open import Type.RenamingSubstitution hiding (subst)
inferVarType : ∀{Φ}(Γ : Ctx Φ) → WeirdFin (len Γ) → Maybe (Σ (Φ ⊢⋆ *) λ A → Γ ∋ A)
inferVarType (Γ ,⋆ J) (WeirdFin.T x) = Utils.map (λ {(A ,, x) → weaken A ,, _∋_.T x}) (inferVarType Γ x)
inferVarType (Γ , A)  Z              = just (A ,, Z)
inferVarType (Γ , A)  (S x)          = Utils.map (λ {(A ,, x) → A ,, S x}) (inferVarType Γ x)

open import Relation.Binary hiding (_⇒_)
dec2maybe : {A : Set}{a a' : A} → Dec (a ≡ a') → Maybe (a ≡ a')
dec2maybe (yes p) = just p
dec2maybe (no ¬p) = nothing

open import Type.BetaNormal
open import Data.String.Properties

meqTyVar : ∀{Φ K}(α α' : Φ ∋⋆ K) → Maybe (α ≡ α')
meqTyVar Z     Z      = just refl
meqTyVar (S α) (S α') = do
  refl ← meqTyVar α α'
  return refl
meqTyVar _     _      = nothing

meqNfTy : ∀{Φ K}(A A' : Φ ⊢Nf⋆ K) → Maybe (A ≡ A')
meqNeTy : ∀{Φ K}(A A' : Φ ⊢Ne⋆ K) → Maybe (A ≡ A')

meqNfTy (A ⇒ B) (A' ⇒ B') = do
 refl ← meqNfTy A A'
 refl ← meqNfTy B B'
 return refl
meqNfTy (ƛ x A) (ƛ x' A') = do
  refl ← dec2maybe (x Data.String.Properties.≟ x') 
  refl ← meqNfTy A A'
  return refl
meqNfTy (con c) (con c')  = nothing -- TODO
meqNfTy (ne n)  (ne n')   = do
  refl ← meqNeTy n n'
  return refl
meqNfTy _      _          = nothing

meqNeTy (` α) (` α')      = do
  refl ← meqTyVar α α'
  return refl
meqNeTy (_·_ {K = K} A B) (_·_ {K = K'} A' B') = do
  refl ← meqKind K K'
  refl ← meqNeTy A A'
  refl ← meqNfTy B B'
  return refl
meqNeTy μ1 μ1 = just refl
meqNeTy _  _  = nothing

open import Type.Equality
open import Type.BetaNBE
open import Type.BetaNBE.Soundness

inv-complete : ∀{Φ K}{A A' : Φ ⊢⋆ K} → nf A ≡ nf A' → A' ≡β A
inv-complete {A = A}{A' = A'} p = trans≡β
  (soundness A')
  (trans≡β (subst (λ A → embNf (nf A') ≡β A) (cong embNf (sym p)) (refl≡β (embNf (nf A'))))
           (sym≡β (soundness A)))

inferType : ∀{Φ}(Γ : Ctx Φ) → ScopedTm (len Γ) → Maybe (Σ (Φ ⊢⋆ *) λ A → Γ ⊢ A)
inferType Γ (` x)             = Utils.map (λ{(A ,, x) → A ,, ` x}) (inferVarType Γ x)
inferType Γ (Λ x K L)         = do
  A ,, L ← inferType (Γ ,⋆ K) L
  return (Π x A ,, Λ x L)
inferType Γ (L ·⋆ A)          = do
  Π {K = K} x B ,, L ← inferType Γ L
    where _ → nothing
  K' ,, A ← bondKind _ A
  refl ← meqKind K K'
  return (B [ A ] ,, L ·⋆ A)
inferType Γ (ƛ x A L)         = do
  * ,, A ← bondKind _ A
    where _ → nothing
  B ,, L ← inferType (Γ , A) L 
  return (A ⇒ B ,, ƛ x L)
inferType Γ (L · M)           = do
  A ⇒ B ,, L ← inferType Γ L
    where _ → nothing
  A' ,, M ← inferType Γ M
  p ← meqNfTy (nf A) (nf A') 
  return (B ,, (L · conv (inv-complete p) M))
inferType Γ (con c)           = nothing -- TODO
inferType Γ (error A)         = do
  * ,, A ← bondKind _ A
    where _ → nothing
  return (A ,, error A)
inferType Γ (builtin bn x x₁) = nothing -- TODO
inferType Γ (wrap pat arg L)  = nothing -- TODO
inferType Γ (unwrap L)        = nothing -- TODO
```
