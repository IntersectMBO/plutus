```
module Check where
```

```
open import Scoped
open import Type
open import Type.BetaNormal
open import Utils hiding (_>>=_)
open import Builtin
open import Type.Equality
open import Type.BetaNBE
open import Type.BetaNBE.Soundness

open import Data.String
open import Data.Nat
open import Data.Fin
open import Data.Product renaming (_,_ to _,,_)
open import Data.Vec hiding ([_];_>>=_)
```

```
len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = 0
len⋆ (Φ ,⋆ K) = suc (len⋆ Φ)

inferTyVar : ∀ Φ (i : Fin (len⋆ Φ)) → Σ Kind (Φ ∋⋆_)
inferTyVar (Φ ,⋆ K) zero    = K ,, Z
inferTyVar (Φ ,⋆ K) (suc i) = let J ,, α = inferTyVar Φ i in  J ,, S α

open import Data.Sum

data Error : Set where
  typeError : Error
  kindEqError : Error
  notTypeError : Error
  notFunction : Error
  notPiError : Error
  notPat : Error
  nameError : String → String → Error 
  typeEqError : ∀{Φ K} → Φ ⊢Nf⋆ K → Φ ⊢Nf⋆ K → Error
  typeVarEqError : Error
  tyConError : Error
  builtinError : Error
  unwrapError : Error  
_>>=_ : {A B C : Set} → A ⊎ C → (A → B ⊎ C) → B ⊎ C
inj₁ a >>= f = f a
inj₂ c >>= f = inj₂ c

return : {A C : Set} → A → A ⊎ C
return = inj₁

open import Data.Bool using (Bool;true;false;_∧_)

eqKind : Kind → Kind → Bool
eqKind * *       = true
eqKind * (_ ⇒ _) = false
eqKind (_ ⇒ _) * = false
eqKind (K ⇒ J) (K' ⇒ J') = eqKind K K' ∧ eqKind J J'

open import Relation.Nullary
open import Relation.Binary using (Decidable)
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

meqKind : (K K' : Kind) → (K ≡ K') ⊎ Error
meqKind * *       = inj₁ refl
meqKind * (_ ⇒ _) = inj₂ kindEqError
meqKind (_ ⇒ _) * = inj₂ kindEqError
meqKind (K ⇒ J) (K' ⇒ J') with meqKind K K'
... | inj₂ e = inj₂ e
... | inj₁ p with meqKind J J'
... | inj₂ e = inj₂ e
... | inj₁ q = inj₁ (cong₂ _⇒_ p q)

inferKind : (Φ : Ctx⋆)(A : ScopedTy (len⋆ Φ)) → (Σ Kind (Φ ⊢Nf⋆_)) ⊎ Error
inferKind Φ (` α) = let K ,, β = inferTyVar Φ α in return (K ,, ne (` β))
inferKind Φ (A ⇒ B) = do
  * ,, A ← inferKind Φ A
    where _ → inj₂ notTypeError
  * ,, B ← inferKind Φ B
    where _ → inj₂ notTypeError
  return (* ,, A ⇒ B)
inferKind Φ (Π K A) = do
  * ,, A ← inferKind (Φ ,⋆ K) A
    where _ → inj₂ notTypeError
  return (* ,, Π A)
inferKind Φ (ƛ K A) = do
  J ,, A ← inferKind (Φ ,⋆ K) A
  return (K ⇒ J ,, ƛ A)
inferKind Φ (A · B) = do
  K ⇒ J ,, A ← inferKind Φ A
    where _ → inj₂ notFunction
  K' ,, B ← inferKind Φ B
  refl ← meqKind K K'
  return (J ,, nf (embNf A · embNf B))
inferKind Φ (con tc)     = inj₁ (* ,, con tc)
inferKind Φ (μ pat arg) = do
  (K ⇒ *) ⇒ K' ⇒ * ,, pat ← inferKind Φ pat
    where _ → inj₂ notPat
  K'' ,, arg ← inferKind Φ arg
  refl ← meqKind K K'
  refl ← meqKind K' K''
  return (* ,, ne (μ1 · pat · arg))
inferKind Φ missing = inj₂ typeError

open import Algorithmic

len : ∀{Φ} → Ctx Φ → Weirdℕ (len⋆ Φ)
len ∅        = Z
len (Γ ,⋆ J) = Weirdℕ.T (len Γ)
len (Γ , A)  = Weirdℕ.S (len Γ)

open import Type.BetaNBE.RenamingSubstitution
open import Function hiding (_∋_)
open import Type.BetaNormal.Equality
inferVarType : ∀{Φ}(Γ : Ctx Φ) → WeirdFin (len Γ) 
  → (Σ (Φ ⊢Nf⋆ *) λ A → Γ ∋ A) ⊎ Error
inferVarType (Γ ,⋆ J) (WeirdFin.T x) = Data.Sum.map (λ {(A ,, x) → weakenNf A ,, _∋_.T x}) id (inferVarType Γ x)
inferVarType (Γ , A)  Z              = inj₁ (A ,, Z)
inferVarType (Γ , A)  (S x)          =
  Data.Sum.map (λ {(A ,, x) → A ,, S x}) id (inferVarType Γ x)

open import Data.String.Properties

open import Relation.Binary hiding (_⇒_)
dec2⊎Err : {a a' : String} → Dec (a ≡ a') → (a ≡ a') ⊎ Error
dec2⊎Err (yes p) = inj₁ p
dec2⊎Err {a}{a'}(no ¬p) = inj₂ (nameError a a')

open import Type.BetaNormal


meqTyVar : ∀{Φ K}(α α' : Φ ∋⋆ K) → (α ≡ α') ⊎ Error
meqTyVar Z     Z      = inj₁ refl
meqTyVar (S α) (S α') = do
  refl ← meqTyVar α α'
  return refl
meqTyVar _     _      = inj₂ typeVarEqError

open import Builtin.Constant.Type

meqTyCon : (c c' : TyCon) → (c ≡ c') ⊎ Error
meqTyCon integer    integer    = return refl
meqTyCon bytestring bytestring = return refl
meqTyCon string     string     = return refl
meqTyCon char       char       = return refl
meqTyCon bool       bool       = return refl
meqTyCon unit       unit       = return refl
meqTyCon _          _          = inj₂ tyConError

meqNfTy : ∀{Φ K}(A A' : Φ ⊢Nf⋆ K) → (A ≡ A') ⊎ Error
meqNeTy : ∀{Φ K}(A A' : Φ ⊢Ne⋆ K) → (A ≡ A') ⊎ Error

meqNfTy (A ⇒ B) (A' ⇒ B') = do
 p ← meqNfTy A A'
 q ← meqNfTy B B'
 return (cong₂ _⇒_ p q)
meqNfTy (ƛ A) (ƛ A') = do
  p ← meqNfTy A A'
  return (cong ƛ p)
meqNfTy (Π {K = K} A) (Π {K = K'} A') = do
  refl ← meqKind K K' 
  p ← meqNfTy A A'
  return (cong Π p)
meqNfTy (con c) (con c')  = do
  refl ← meqTyCon c c'
  return refl
meqNfTy (ne n)  (ne n')   = do
  p ← meqNeTy n n'
  return (cong ne p)
meqNfTy n      n'          = inj₂ (typeEqError n n')

meqNeTy (` α) (` α')      = do
  refl ← meqTyVar α α'
  return refl
meqNeTy (_·_ {K = K} A B) (_·_ {K = K'} A' B') = do
  refl ← meqKind K K'
  p ← meqNeTy A A'
  q ← meqNfTy B B'
  return (cong₂ _·_ p q)
meqNeTy μ1 μ1 = return refl
meqNeTy n  n'  = inj₂ (typeEqError (ne n) (ne n'))

open import Type.BetaNormal.Equality

inv-complete : ∀{Φ K}{A A' : Φ ⊢⋆ K} → nf A ≡ nf A' → A' ≡β A
inv-complete {A = A}{A' = A'} p = trans≡β
  (soundness A')
  (trans≡β (≡2β (sym (cong embNf p))) (sym≡β (soundness A)))

open import Function
import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con as A
open import Builtin.Signature Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Type.RenamingSubstitution

inferTypeCon : ∀{Φ} → TermCon → Σ TyCon λ c → A.TermCon {Φ} (con c) 
inferTypeCon (integer i)    = integer ,, A.integer i
inferTypeCon (bytestring b) = bytestring ,, A.bytestring b
inferTypeCon (string s)     = string ,, A.string s
inferTypeCon (bool b)       = bool ,, A.bool b
inferTypeCon (char c)       = char ,, A.char c
inferTypeCon unit           = unit ,, A.unit

inferType : ∀{Φ}(Γ : Ctx Φ) → ScopedTm (len Γ)
  → (Σ (Φ ⊢Nf⋆ *) λ A → Γ ⊢ A) ⊎ Error

inferTypeBuiltin : ∀{Φ m n}{Γ : Ctx Φ}(bn : Builtin)
  → Tel⋆ (len⋆ Φ) m → Scoped.Tel (len Γ) n
  → (Σ (Φ ⊢Nf⋆ *) (Γ ⊢_)) ⊎ Error
inferTypeBuiltin addInteger [] [] = return ((con integer ⇒ con integer ⇒ con integer) ,, ƛ (ƛ (builtin addInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin subtractInteger [] [] = return ((con integer ⇒ con integer ⇒ con integer) ,, ƛ (ƛ (builtin subtractInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin multiplyInteger [] [] = return ((con integer ⇒ con integer ⇒ con integer) ,, ƛ (ƛ (builtin multiplyInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin divideInteger [] [] = return ((con integer ⇒ con integer ⇒ con integer) ,, ƛ (ƛ (builtin divideInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin quotientInteger [] [] = return ((con integer ⇒ con integer ⇒ con integer) ,, ƛ (ƛ (builtin quotientInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin remainderInteger [] [] = return ((con integer ⇒ con integer ⇒ con integer) ,, ƛ (ƛ (builtin remainderInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin modInteger [] []  = return ((con integer ⇒ con integer ⇒ con integer) ,, ƛ (ƛ (builtin modInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin lessThanInteger [] [] = return ((con integer ⇒ con integer ⇒ con bool) ,, ƛ (ƛ (builtin lessThanInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin lessThanEqualsInteger [] [] = return ((con integer ⇒ con integer ⇒ con bool) ,, ƛ (ƛ (builtin lessThanEqualsInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin greaterThanInteger [] [] = return ((con integer ⇒ con integer ⇒ con bool) ,, ƛ (ƛ (builtin greaterThanInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin greaterThanEqualsInteger [] [] = return ((con integer ⇒ con integer ⇒ con bool) ,, ƛ (ƛ (builtin greaterThanEqualsInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin equalsInteger [] [] = return ((con integer ⇒ con integer ⇒ con bool) ,, ƛ (ƛ (builtin equalsInteger (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin concatenate [] [] = return ((con bytestring ⇒ con bytestring ⇒ con bytestring) ,, ƛ (ƛ (builtin concatenate (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin takeByteString [] [] = return ((con integer ⇒ con bytestring ⇒ con bytestring) ,, ƛ (ƛ (builtin takeByteString (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin dropByteString [] [] = return ((con integer ⇒ con bytestring ⇒ con bytestring) ,, ƛ (ƛ (builtin dropByteString (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin sha2-256 [] [] = return ((con bytestring ⇒ con bytestring) ,, ƛ (builtin sha2-256 (λ()) (` Z ∷ [])))
inferTypeBuiltin sha3-256 [] [] = return ((con bytestring ⇒ con bytestring) ,, ƛ (builtin sha3-256 (λ()) (` Z ∷ [])))
inferTypeBuiltin verifySignature [] [] = return ((con bytestring ⇒ con bytestring ⇒ con bytestring ⇒ con bool) ,, ƛ (ƛ (ƛ (builtin verifySignature (λ()) (` (S (S Z)) ∷ ` (S Z) ∷ (` Z) ∷ [])))))
inferTypeBuiltin equalsByteString [] [] = return ((con bytestring ⇒ con bytestring ⇒ con bool) ,, ƛ (ƛ (builtin equalsByteString (λ()) (` (S Z) ∷ ` Z ∷ []))))
inferTypeBuiltin ifThenElse [] [] = return (Π (con bool ⇒ ne (` Z) ⇒ ne (` Z) ⇒ ne (` Z)) ,, Λ (ƛ (ƛ (ƛ (builtin ifThenElse (λ { Z → ne (` Z)}) (` (S (S Z)) ∷ ` (S Z) ∷ ` Z ∷ []))))))
inferTypeBuiltin _ _ _ = inj₂ builtinError


inferType Γ (` x)             =
  Data.Sum.map (λ{(A ,, x) → A ,, ` x}) id (inferVarType Γ x)
inferType Γ (Λ K L)         = do
  A ,, L ← inferType (Γ ,⋆ K) L
  return (Π A ,, Λ L)
inferType Γ (L ·⋆ A)          = do
  Π {K = K} B ,, L ← inferType Γ L
    where _ → inj₂ notPiError
  K' ,, A ← inferKind _ A
  refl ← meqKind K K'
  return (B [ A ]Nf ,, (_·⋆_ L A))
inferType Γ (ƛ A L)         = do
  * ,, A ← inferKind _ A
    where _ → inj₂ notTypeError
  B ,, L ← inferType (Γ , A) L 
  return (A ⇒ B ,, ƛ L)
inferType Γ (L · M)           = do
  A ⇒ B ,, L ← inferType Γ L
    where _ → inj₂ notFunction
  A' ,, M ← inferType Γ M
  p ← meqNfTy A A'
  return (B ,, (L · conv⊢ refl (sym p) M))
inferType {Φ} Γ (con c)           = let
  tc ,, c = inferTypeCon {Φ} c in return (con tc ,, con c)
inferType Γ (error A)         = do
  * ,, A ← inferKind _ A
    where _ → inj₂ notTypeError
  return (A ,, error A)
inferType Γ (builtin bn p As ts) = inferTypeBuiltin bn As ts
inferType Γ (wrap pat arg L)  = do
  (K ⇒ *) ⇒ K' ⇒ * ,, pat ← inferKind _ pat
    where _ → inj₂ notPat
  K'' ,, arg ← inferKind _ arg
  refl ← meqKind K K'
  refl ← meqKind K' K''
  X ,, L ← inferType Γ L
  --v why is this eta expanded in the spec?
  p ← meqNfTy (nf (embNf pat · (μ1 · embNf pat) · embNf arg)) X
  return
    (ne (μ1 · pat · arg)
    ,,
    wrap1 pat arg (conv⊢ refl (sym p) L))
inferType Γ (unwrap L)        = do
  ne (μ1 · pat · arg) ,, L ← inferType Γ L
    where _ → inj₂ unwrapError
  --v why is this eta expanded in the spec?
  return (nf (embNf pat · (μ1 · embNf pat) · embNf arg) ,, unwrap1 L)
```
