```
module Check where
```

```
open import Scoped
open import Type
open import Type.BetaNormal
open import Utils
open import Builtin
open import Type.Equality
open import Type.BetaNBE
open import Type.BetaNBE.Soundness

open import Data.Nat
open import Data.Fin
open import Data.Product renaming (_,_ to _,,_)
open import Data.List hiding ([_])
```

```
len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = 0
len⋆ (Φ ,⋆ K) = suc (len⋆ Φ)

inferTyVar : ∀ Φ (i : Fin (len⋆ Φ)) → Σ Kind (Φ ∋⋆_)
inferTyVar (Φ ,⋆ K) zero    = K ,, Z
inferTyVar (Φ ,⋆ K) (suc i) = let J ,, α = inferTyVar Φ i in  J ,, S α

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

inferKind : (Φ : Ctx⋆)(A : ScopedTy (len⋆ Φ)) → Maybe (Σ Kind (Φ ⊢Nf⋆_))
inferKind Φ (` α) = let K ,, β = inferTyVar Φ α in return (K ,, ne (` β))
inferKind Φ (A ⇒ B) = do
  * ,, A ← inferKind Φ A
    where _ → nothing
  * ,, B ← inferKind Φ B
    where _ → nothing
  return (* ,, A ⇒ B)
inferKind Φ (Π x K A) = do
  * ,, A ← inferKind (Φ ,⋆ K) A
    where _ → nothing
  return (* ,, Π x A)
inferKind Φ (ƛ x K A) = do
  J ,, A ← inferKind (Φ ,⋆ K) A
  return (K ⇒ J ,, ƛ x A)
inferKind Φ (A · B) = do
  K ⇒ J ,, A ← inferKind Φ A
    where _ → nothing
  K' ,, B ← inferKind Φ B
  refl ← meqKind K K'
  return (J ,, nf (embNf A · embNf B))
inferKind Φ (con tc)     = just (* ,, con tc)
inferKind Φ (μ pat arg) = do
  (K ⇒ *) ⇒ K' ⇒ * ,, pat ← inferKind Φ pat
    where _ → nothing
  K'' ,, arg ← inferKind Φ arg
  refl ← meqKind K K'
  refl ← meqKind K' K''
  return (* ,, ne (μ1 · pat · arg))

open import Algorithmic

len : ∀{Φ} → Ctx Φ → Weirdℕ (len⋆ Φ)
len ∅        = Z
len (Γ ,⋆ J) = Weirdℕ.T (len Γ)
len (Γ , A)  = Weirdℕ.S (len Γ)

open import Type.BetaNBE.RenamingSubstitution

inferVarType : ∀{Φ}(Γ : Ctx Φ) → WeirdFin (len Γ) → Maybe (Σ (Φ ⊢Nf⋆ *) λ A → Γ ∋ A)
inferVarType (Γ ,⋆ J) (WeirdFin.T x) = Utils.map (λ {(A ,, x) → weakenNf A ,, _∋_.T x}) (inferVarType Γ x)
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

open import Builtin.Constant.Type

meqTyCon : (c c' : TyCon) → Maybe (c ≡ c')
meqTyCon integer    integer    = just refl
meqTyCon bytestring bytestring = just refl
meqTyCon string     string     = just refl
meqTyCon _          _          = nothing

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
meqNfTy (con c) (con c')  = do
  refl ← meqTyCon c c'
  return refl
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


inv-complete : ∀{Φ K}{A A' : Φ ⊢⋆ K} → nf A ≡ nf A' → A' ≡β A
inv-complete {A = A}{A' = A'} p = trans≡β
  (soundness A')
  (trans≡β (subst (λ A → embNf (nf A') ≡β A) (cong embNf (sym p)) (refl≡β (embNf (nf A'))))
           (sym≡β (soundness A)))

open import Function
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as A
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf
open import Type.RenamingSubstitution

inferTypeCon : ∀{Φ} → TermCon → Σ TyCon λ c → A.TermCon {Φ} (con c) 
inferTypeCon (integer i)    = integer ,, A.integer i
inferTypeCon (bytestring b) = bytestring ,, A.bytestring b
inferTypeCon (string s)     = string ,, A.string s

inferType : ∀{Φ}(Γ : Ctx Φ) → ScopedTm (len Γ) → Maybe (Σ (Φ ⊢Nf⋆ *) λ A → Γ ⊢ A)

inferTypeBuiltin : ∀{Φ}{Γ : Ctx Φ}(bn : Builtin) → List (ScopedTy (len⋆ Φ)) → List (ScopedTm (len Γ))
  → Maybe (Σ (Φ ⊢Nf⋆ *) (Γ ⊢_))
inferTypeBuiltin addInteger [] [] = just ((con integer ⇒ con integer ⇒ con integer) ,, ƛ "" (ƛ "" (builtin addInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin subtractInteger [] [] = just ((con integer ⇒ con integer ⇒ con integer) ,, ƛ "" (ƛ "" (builtin subtractInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin multiplyInteger [] [] = just ((con integer ⇒ con integer ⇒ con integer) ,, ƛ "" (ƛ "" (builtin multiplyInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin divideInteger [] [] = just ((con integer ⇒ con integer ⇒ con integer) ,, ƛ "" (ƛ "" (builtin divideInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin quotientInteger [] [] = just ((con integer ⇒ con integer ⇒ con integer) ,, ƛ "" (ƛ "" (builtin quotientInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin remainderInteger [] [] = just ((con integer ⇒ con integer ⇒ con integer) ,, ƛ "" (ƛ "" (builtin remainderInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin modInteger [] []  = just ((con integer ⇒ con integer ⇒ con integer) ,, ƛ "" (ƛ "" (builtin modInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin lessThanInteger [] [] = just ((con integer ⇒ con integer ⇒ booleanNf) ,, ƛ "" (ƛ "" (builtin lessThanInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin lessThanEqualsInteger [] [] = just ((con integer ⇒ con integer ⇒ booleanNf) ,, ƛ "" (ƛ "" (builtin lessThanEqualsInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin greaterThanInteger [] [] = just ((con integer ⇒ con integer ⇒ booleanNf) ,, ƛ "" (ƛ "" (builtin greaterThanInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin greaterThanEqualsInteger As ts = just ((con integer ⇒ con integer ⇒ booleanNf) ,, ƛ "" (ƛ "" (builtin greaterThanEqualsInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin equalsInteger As ts = just ((con integer ⇒ con integer ⇒ booleanNf) ,, ƛ "" (ƛ "" (builtin equalsInteger (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin concatenate [] [] = just ((con bytestring ⇒ con bytestring ⇒ con bytestring) ,, ƛ "" (ƛ "" (builtin concatenate (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin takeByteString [] [] = just ((con integer ⇒ con bytestring ⇒ con bytestring) ,, ƛ "" (ƛ "" (builtin takeByteString (λ()) (` (S Z) ,, ` Z ,, _))))
inferTypeBuiltin dropByteString [] [] = just ((con integer ⇒ con bytestring ⇒ con bytestring) ,, ƛ "" (ƛ "" (builtin dropByteString (λ()) (` (S Z) ,, ` Z ,, _))))
{-
inferTypeBuiltin sha2-256 As ts = {!!}
inferTypeBuiltin sha3-256 As ts = {!!}
inferTypeBuiltin verifySignature As ts = {!!}
inferTypeBuiltin equalsByteString As ts = {!!}
-}
inferTypeBuiltin _ _ _ = nothing

inferType Γ (` x)             = Utils.map (λ{(A ,, x) → A ,, ` x}) (inferVarType Γ x)
inferType Γ (Λ x K L)         = do
  A ,, L ← inferType (Γ ,⋆ K) L
  return (Π x A ,, Λ x L)
inferType Γ (L ·⋆ A)          = do
  Π {K = K} x B ,, L ← inferType Γ L
    where _ → nothing
  K' ,, A ← inferKind _ A
  refl ← meqKind K K'
  return (B [ A ]Nf ,, (L ·⋆ A))
inferType Γ (ƛ x A L)         = do
  * ,, A ← inferKind _ A
    where _ → nothing
  B ,, L ← inferType (Γ , A) L 
  return (A ⇒ B ,, ƛ x L)
inferType Γ (L · M)           = do
  A ⇒ B ,, L ← inferType Γ L
    where _ → nothing
  A' ,, M ← inferType Γ M
  refl ← meqNfTy A A'
  return (B ,, (L · M))
inferType {Φ} Γ (con c)           = let
  tc ,, c = inferTypeCon {Φ} c in just (con tc ,, con c)
inferType Γ (error A)         = do
  * ,, A ← inferKind _ A
    where _ → nothing
  return (A ,, error A)
inferType Γ (builtin bn As ts) = inferTypeBuiltin bn As ts
inferType Γ (wrap pat arg L)  = do
  (K ⇒ *) ⇒ K' ⇒ * ,, pat ← inferKind _ pat
    where _ → nothing
  K'' ,, arg ← inferKind _ arg
  refl ← meqKind K K'
  refl ← meqKind K' K''
  X ,, L ← inferType Γ L
  --v why is this eta expanded in the spec?
  refl ← meqNfTy (nf (embNf pat · (μ1 · embNf pat) · embNf arg)) X
  return
    (ne (μ1 · pat · arg)
    ,,
    wrap1 pat arg L)
inferType Γ (unwrap L)        = do
  ne (μ1 · pat · arg) ,, L ← inferType Γ L
    where _ → nothing
  --v why is this eta expanded in the spec?
  return (nf (embNf pat · (μ1 · embNf pat) · embNf arg) ,, unwrap1 L)
  
```
