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
open import Algorithmic
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal.Equality
open import Builtin.Constant.Type

open import Function hiding (_∋_)
open import Data.String
open import Data.Nat hiding (_*_)
open import Data.Fin
open import Data.Product renaming (_,_ to _,,_) hiding (map)
open import Data.Vec hiding ([_];_>>=_) hiding (map)
import Data.List as L
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
```

```
len⋆ : Ctx⋆ → ℕ
len⋆ ∅        = 0
len⋆ (Φ ,⋆ K) = suc (len⋆ Φ)

inferTyVar : ∀ Φ (i : Fin (len⋆ Φ)) → Σ Kind (Φ ∋⋆_)
inferTyVar (Φ ,⋆ K) zero    = K ,, Z
inferTyVar (Φ ,⋆ K) (suc i) = let J ,, α = inferTyVar Φ i in  J ,, S α

⊎bind : {A B C : Set} → A ⊎ C → (A → B ⊎ C) → B ⊎ C
⊎bind (inj₁ a) f = f a
⊎bind (inj₂ c) f = inj₂ c

data TypeError : Set where
  kindMismatch : (K K' : Kind) → ¬ (K ≡ K') → TypeError
  notStar : (K : Kind) → ¬ (K ≡ *) → TypeError
  notFunKind  : (K : Kind) → (∀ K' J → ¬ (K ≡ K' ⇒ J)) → TypeError
  notPat  : (K : Kind) → (∀ K' → ¬ (K ≡ (K' ⇒ *) ⇒ (K' ⇒ *))) → TypeError
  UnknownType : TypeError
  notPi  : ∀{Φ}(A : Φ ⊢Nf⋆ *) → (∀{K}(A' : Φ ,⋆ K ⊢Nf⋆ *) → ¬ (A ≡ Π A')) →
    TypeError
  notMu : ∀{Φ}(A : Φ ⊢Nf⋆ *) → (∀{K}(A' : Φ ⊢Nf⋆ _)(B : Φ ⊢Nf⋆ K) → ¬ (A ≡ μ A' B))
    → TypeError
  notFunType : ∀{Φ}(A : Φ ⊢Nf⋆ *) → ((A' B : Φ ⊢Nf⋆ *) → ¬ (A ≡ A' ⇒ B)) → TypeError
  typeMismatch : ∀{Φ K}(A A' : Φ ⊢Nf⋆ K) → ¬ (A ≡ A') → TypeError
  builtinError : TypeError

meqKind : (K K' : Kind) → Either (¬ (K ≡ K')) (K ≡ K')
meqKind * * = inj₂ refl
meqKind * (K' ⇒ J') = inj₁ λ() 
meqKind (K ⇒ J) * = inj₁ λ()
meqKind (K ⇒ J) (K' ⇒ J') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqKind K K')
  q ← withE (λ ¬q → λ{refl → ¬q refl}) (meqKind J J')
  return (cong₂ _⇒_ p q)

isStar : ∀{Φ}
       → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))
       → Either TypeError (Φ ⊢Nf⋆ *)
isStar p = do
  * ,, A ← p
   where (K ⇒ J ,, _) → inj₁ (notStar (K ⇒ J) λ())
  return A

isFunKind : ∀{Φ}
       → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))
       → Either TypeError (Σ Kind λ K → Σ Kind λ J → Φ ⊢Nf⋆ K ⇒ J)
isFunKind p = do
  K ⇒ J ,, A ← p
    where (* ,, _) → inj₁ (notFunKind * λ _ _ ())
  return (K ,, J ,, A)

isPat : ∀{Φ}
       → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))
       → Either TypeError (Σ Kind λ K → Φ ⊢Nf⋆ (K ⇒ *) ⇒ (K ⇒ *))
isPat p = do
  (K ⇒ *) ⇒ (K' ⇒ *) ,, A ← p
    where
      (* ,, _) → inj₁ (notPat * λ _ ())
      (K@(_ ⇒ *) ,, _) → inj₁ (notPat K λ _ ())
      (K@(_ ⇒ (_ ⇒ (_ ⇒ _))) ,, _) → inj₁ (notPat K λ _ ())
      (K@(* ⇒ (_ ⇒ *)) ,, _) → inj₁ (notPat K λ _ ())
      (K@((_ ⇒ (_ ⇒ _)) ⇒ (_ ⇒ *)) ,, _) → inj₁ (notPat K λ _ ())
  refl ← withE (kindMismatch _ _) (meqKind K K')
  return (K ,, A)

isPi :  ∀{Φ Γ}
       → Either TypeError (Σ (Φ ⊢Nf⋆ *) (Γ ⊢_))
       → Either TypeError (Σ Kind λ K → Σ (Φ ,⋆ K ⊢Nf⋆ *) λ A → Γ ⊢ Π A)
isPi p = do
  Π A ,, L ← p
    where A ⇒ B ,, _ → inj₁ (notPi (A ⇒ B) (λ _ ()))
          ne A  ,, _ → inj₁ (notPi (ne A) (λ _ ()))
          con {Φ} c ,, _ → inj₁ (notPi (con {Φ} c) (λ _ ()))
          μ A B ,, _ → inj₁ (notPi (μ A B) (λ _ ()))
  return (_ ,, A ,, L)

isFunType :  ∀{Φ Γ}
       → Either TypeError (Σ (Φ ⊢Nf⋆ *) (Γ ⊢_))
       → Either TypeError (Σ (Φ ⊢Nf⋆ *) λ A → Σ (Φ ⊢Nf⋆ *) λ B → Γ ⊢ A ⇒ B)
isFunType p = do
  A ⇒ B ,, L ← p
    where Π A ,, _ → inj₁ (notFunType (Π A) (λ _ _ ()))
          ne A  ,, _ → inj₁ (notFunType (ne A) (λ _ _ ()))
          con {Φ} c ,, _ → inj₁ (notFunType (con {Φ} c) (λ _ _ ()))
          μ A B ,, _ → inj₁ (notFunType (μ A B) (λ _ _ ()))
  return (A ,, B ,, L)
  
isMu :  ∀{Φ Γ}
       → Either TypeError (Σ (Φ ⊢Nf⋆ *) (Γ ⊢_))
       → Either TypeError (Σ Kind λ K → Σ (Φ ⊢Nf⋆ (K ⇒ *) ⇒ (K ⇒ *)) λ A → Σ (Φ ⊢Nf⋆ K) λ B → Γ ⊢ μ A B)
isMu p = do
  μ A B ,, L ← p
    where Π A ,, _ → inj₁ (notMu (Π A) (λ _ _ ()))
          ne A  ,, _ → inj₁ (notMu (ne A) (λ _ _ ()))
          con {Φ} c ,, _ → inj₁ (notMu (con {Φ} c) (λ _ _ ()))
          A ⇒ B ,, _ → inj₁ (notMu (A ⇒ B) (λ _ _ ()))
  return (_ ,, A ,, B ,, L)

checkKind : ∀ Φ (A : ScopedTy (len⋆ Φ)) → ∀ K → Either TypeError (Φ ⊢Nf⋆ K)
inferKind : ∀ Φ (A : ScopedTy (len⋆ Φ)) → Either TypeError (Σ Kind (Φ ⊢Nf⋆_))

checkKind Φ A K = do
  K' ,, A ← inferKind Φ A
  refl ← withE (kindMismatch _ _) (meqKind K K')
  return A

inferKind Φ (` α) = let K ,, β = inferTyVar Φ α in return (K ,, ne (` β))
inferKind Φ (A ⇒ B) = do
  A ← isStar (inferKind Φ A)
  B ← isStar (inferKind Φ B)
  return (* ,, A ⇒ B)
inferKind Φ (Π K A) = do
  A ← isStar (inferKind (Φ ,⋆ K) A)
  return (* ,, Π A)
inferKind Φ (ƛ K A) = do
  J ,, A ← inferKind (Φ ,⋆ K) A
  return (K ⇒ J ,, ƛ A)
inferKind Φ (A · B) = do
  (K ,, J ,, A) ← isFunKind (inferKind Φ A)
  B ← checkKind Φ B K
  return (J ,, nf (embNf A · embNf B))
inferKind Φ (con tc) = return (* ,, con tc)
inferKind Φ (μ A B) = do
  K ,, A ← isPat (inferKind Φ A)
  B ← checkKind Φ B K
  return (* ,, μ A B)
inferKind Φ missing = inj₁ UnknownType

len : ∀{Φ} → Ctx Φ → Weirdℕ (len⋆ Φ)
len ∅        = Z
len (Γ ,⋆ J) = Weirdℕ.T (len Γ)
len (Γ , A)  = Weirdℕ.S (len Γ)

inferVarType : ∀{Φ}(Γ : Ctx Φ) → WeirdFin (len Γ) 
  → Either TypeError (Σ (Φ ⊢Nf⋆ *) λ A → Γ ∋ A)
inferVarType (Γ ,⋆ J) (WeirdFin.T x) = do
  A ,, α ← inferVarType Γ x
  return (weakenNf A ,, T α)
inferVarType (Γ , A) Z = return (A ,, Z)
inferVarType (Γ , A) (S x) = do
  A ,, α ← inferVarType Γ x
  return (A ,, S α)

meqTyVar : ∀{Φ K}(α α' : Φ ∋⋆ K) → Either (¬ (α ≡ α')) (α ≡ α')
meqTyVar Z     Z      = inj₂ refl 
meqTyVar (S α) (S α') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqTyVar α α')
  return (cong S p)
meqTyVar Z     (S α') = inj₁ λ()
meqTyVar (S α) Z      = inj₁ λ()

meqTyCon : (c c' : TyCon) → Either (¬ (c ≡ c')) (c ≡ c')
meqTyCon integer    integer    = inj₂ refl
meqTyCon bytestring bytestring = inj₂ refl
meqTyCon string     string     = inj₂ refl
meqTyCon char       char       = inj₂ refl
meqTyCon bool       bool       = inj₂ refl
meqTyCon unit       unit       = inj₂ refl
meqTyCon integer    bytestring = inj₁ λ()
meqTyCon integer    string     = inj₁ λ()
meqTyCon integer    char       = inj₁ λ()
meqTyCon integer    unit       = inj₁ λ()
meqTyCon integer    bool       = inj₁ λ()
meqTyCon bytestring integer    = inj₁ λ()
meqTyCon bytestring string     = inj₁ λ()
meqTyCon bytestring char       = inj₁ λ()
meqTyCon bytestring unit       = inj₁ λ()
meqTyCon bytestring bool       = inj₁ λ()
meqTyCon string     integer    = inj₁ λ()
meqTyCon string     bytestring = inj₁ λ()
meqTyCon string     char       = inj₁ λ()
meqTyCon string     unit       = inj₁ λ()
meqTyCon string     bool       = inj₁ λ()
meqTyCon char       integer    = inj₁ λ()
meqTyCon char       bytestring = inj₁ λ()
meqTyCon char       string     = inj₁ λ()
meqTyCon char       unit       = inj₁ λ()
meqTyCon char       bool       = inj₁ λ()
meqTyCon unit       integer    = inj₁ λ()
meqTyCon unit       bytestring = inj₁ λ()
meqTyCon unit       string     = inj₁ λ()
meqTyCon unit       char       = inj₁ λ()
meqTyCon unit       bool       = inj₁ λ()
meqTyCon bool       integer    = inj₁ λ()
meqTyCon bool       bytestring = inj₁ λ()
meqTyCon bool       string     = inj₁ λ()
meqTyCon bool       char       = inj₁ λ()
meqTyCon bool       unit       = inj₁ λ()

meqNfTy : ∀{Φ K}(A A' : Φ ⊢Nf⋆ K) → Either (¬ (A ≡ A')) (A ≡ A')
meqNeTy : ∀{Φ K}(A A' : Φ ⊢Ne⋆ K) → Either (¬ (A ≡ A')) (A ≡ A')

meqNfTy (A ⇒ B) (A' ⇒ B') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqNfTy A A')
  q ← withE (λ ¬q → λ{refl → ¬q refl}) (meqNfTy B B')
  return (cong₂ _⇒_ p q)
meqNfTy (ƛ A) (ƛ A') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqNfTy A A')
  return (cong ƛ p)
meqNfTy (Π {K = K} A) (Π {K = K'} A') = do
 refl ← withE (λ ¬p → λ{refl → ¬p refl}) (meqKind K K')
 q    ← withE (λ ¬q → λ{refl → ¬q refl}) (meqNfTy A A')
 return (cong Π q)
meqNfTy (con c) (con c') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqTyCon c c')
  return (cong con p)
meqNfTy (μ {K = K} A B) (μ {K = K'} A' B') = do
  refl ← withE (λ ¬p → λ{refl → ¬p refl}) (meqKind K K')
  q    ← withE (λ ¬q → λ{refl → ¬q refl}) (meqNfTy A A')
  r    ← withE (λ ¬r → λ{refl → ¬r refl}) (meqNfTy B B')
  return (cong₂ μ q r)
meqNfTy (ne A) (ne A') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqNeTy A A')
  return (cong ne p)
meqNfTy (Π _) (_ ⇒ _) = inj₁ λ()
meqNfTy (Π _) (ne _) = inj₁ λ()
meqNfTy (Π _) (con _) = inj₁ λ()
meqNfTy (Π _) (μ _ _) = inj₁ λ()
meqNfTy (_ ⇒ _) (Π _) = inj₁ λ()
meqNfTy (_ ⇒ _) (ne _) = inj₁ λ()
meqNfTy (_ ⇒ _) (con _) = inj₁ λ()
meqNfTy (_ ⇒ _) (μ _ _) = inj₁ λ()
meqNfTy (ƛ _) (ne _) = inj₁ λ()
meqNfTy (ne _) (Π _) = inj₁ λ()
meqNfTy (ne _) (_ ⇒ _) = inj₁ λ()
meqNfTy (ne _) (ƛ _) = inj₁ λ()
meqNfTy (ne _) (con _) = inj₁ λ()
meqNfTy (ne _) (μ _ _) = inj₁ λ()
meqNfTy (con _) (Π _) = inj₁ λ()
meqNfTy (con _) (_ ⇒ _) = inj₁ λ()
meqNfTy (con _) (ne _) = inj₁ λ()
meqNfTy (con _) (μ _ _) = inj₁ λ()
meqNfTy (μ _ _) (Π _) = inj₁ λ()
meqNfTy (μ _ _) (_ ⇒ _) = inj₁ λ()
meqNfTy (μ _ _) (ne _) = inj₁ λ()
meqNfTy (μ _ _) (con _) = inj₁ λ()

meqNeTy (` α) (` α') = do
  p ← withE (λ ¬p → λ{refl → ¬p refl}) (meqTyVar α α')
  return (cong ` p)
meqNeTy (_·_ {K = K} A B) (_·_ {K = K'} A' B') = do
  refl ← withE (λ ¬p → λ{refl → ¬p refl}) (meqKind K K')
  q    ← withE (λ ¬q → λ{refl → ¬q refl}) (meqNeTy A A')
  r    ← withE (λ ¬r → λ{refl → ¬r refl}) (meqNfTy B B')
  return (cong₂ _·_ q r)
meqNeTy (` _) (_ · _) = inj₁ λ()
meqNeTy (_ · _) (` _) = inj₁ λ()

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

checkType : ∀{Φ}(Γ : Ctx Φ) → ScopedTm (len Γ) → (A : Φ ⊢Nf⋆ *)
  → Either TypeError (Γ ⊢ A)

inferType : ∀{Φ}(Γ : Ctx Φ) → ScopedTm (len Γ)
  → Either TypeError (Σ (Φ ⊢Nf⋆ *) λ A → Γ ⊢ A)

checkType Γ L A = do
  A' ,, L ← inferType Γ L
  refl ← withE (typeMismatch _ _) (meqNfTy A A')
  return L
  
inferTypeBuiltin : ∀{Φ m n}{Γ : Ctx Φ}(bn : Builtin)
  → Tel⋆ (len⋆ Φ) m → Scoped.Tel (len Γ) n
  → Either TypeError (Σ (Φ ⊢Nf⋆ *) (Γ ⊢_))
inferTypeBuiltin b [] [] = let Φ ,, As ,, C = SIG b in
  inj₂ (_ ,, ibuiltin b)
inferTypeBuiltin _ _ _ = inj₁ builtinError
  
inferType Γ (` x) = do
  A ,, α ← inferVarType Γ x
  return (A ,, ` α)
inferType Γ (Λ K L) = do
  A ,, L ← inferType (Γ ,⋆ K) L
  return (Π A ,, Λ L)
inferType Γ (L ·⋆ A) = do
  K ,, B ,, L ← isPi (inferType Γ L)
  A ← checkKind _ A K
  return (B [ A ]Nf ,, L ·⋆ A)
inferType Γ (ƛ A L) = do
  A ← isStar (inferKind _ A)
  B ,, L ← inferType (Γ , A) L 
  return (A ⇒ B ,, ƛ L)
inferType {Φ} Γ (L · M) = do
  A ,, B ,, L ← isFunType (inferType Γ L)
  M ← checkType Γ M A
  return (B ,, L · M)
inferType {Φ} Γ (con c) = do
  let tc ,, c = inferTypeCon {Φ} c
  return (con tc ,, con c)
inferType Γ (error A) = do
  A ← isStar (inferKind _ A)
  return (A ,, error A)
inferType Γ (builtin bn p As ts) = inferTypeBuiltin bn As ts
inferType Γ (ibuiltin b) = inj₂ (itype b ,, ibuiltin b)
inferType Γ (wrap A B L) = do
  K ,, A ← isPat (inferKind _ A)
  B ← checkKind _ B K
  L ← checkType Γ L (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  return (μ A B ,, wrap A B L)
inferType Γ (unwrap L) = do
  K ,, A ,, B ,, L ← isMu (inferType Γ L)
  return (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B) ,, unwrap L)
```
