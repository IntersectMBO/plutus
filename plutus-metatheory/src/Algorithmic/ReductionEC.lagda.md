```
module Algorithmic.ReductionEC where
```
## Imports

```
open import Agda.Builtin.String using (primStringAppend ; primStringEquality)
open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Fin using (Fin;zero;suc)
open import Data.Bool using (Bool;true;false)
open import Data.Empty using (⊥;⊥-elim)
open import Data.Integer using (_<?_;∣_∣;_≤?_;_≟_)
open import Data.Vec as Vec using (Vec;[];_∷_;lookup)
open import Data.Maybe using (just;from-just)
open import Data.Product using (_×_;∃;proj₁;proj₂) renaming (_,_ to _,,_)
open import Data.String using (String)
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Nullary using (¬_;yes;no)
open import Relation.Binary.PropositionalEquality 
                    using (_≡_;refl;sym;trans;cong)  
                    renaming (subst to substEq)
open import Relation.Binary.HeterogeneousEquality 
        using (_≅_;refl;≅-to-≡) 

open import Utils hiding (List;length;map)
open import Utils.List
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z)
open _⊢⋆_
import Type.RenamingSubstitution as T
open import Algorithmic using (Ctx;_⊢_;conv⊢;⟦_⟧;ConstrArgs;Cases;lookupCase;mkCaseType)
open import Algorithmic.Signature using (btype;_[_]SigTy)
open Ctx
open _⊢_
open import Algorithmic.RenamingSubstitution using (_[_];_[_]⋆)
open import Algorithmic.Properties using (lem-·⋆;lem-unwrap)
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution using (_[_]Nf)
open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;embNf;weakenNf)
open _⊢Nf⋆_
open _⊢Ne⋆_
open import Builtin 
open import Builtin.Constant.Type using (TyCon)

open import Builtin.Signature using (Sig;sig;Args;_⊢♯;args♯;fv)
open Sig

open Builtin.Signature.FromSig _⊢Nf⋆_ _⊢Ne⋆_ ne ` _·_ ^ con _⇒_   Π 
    using (sig2type;SigTy;sig2SigTy;sigTy2type;saturatedSigTy;convSigTy)
open SigTy

import Algorithmic.CEK as CEK
```


## Values

Values are indexed by terms
List of values are indexed by list of terms.

``` 
data Value : {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Set

-- List of Values
VList : ∀{ts} → IBwd (∅ ⊢_) ts → Set
VList = IIBwd Value 

deval : {A : ∅ ⊢Nf⋆ *}{u : ∅ ⊢ A} → Value u → ∅ ⊢ A
deval {u = u} _ = u

deval-VecList : ∀{n} → (A : Vec (List (∃ (∅ ⊢_))) n) → Vec (List (∅ ⊢Nf⋆ *)) n
deval-VecList [] = []
deval-VecList (xs ∷ xss) = map proj₁ xs ∷ (deval-VecList xss)

data BApp (b : Builtin) : 
    ∀{tn tm tt} → {pt : tn ∔ tm ≣ tt}
  → ∀{an am at} → {pa : an ∔ am ≣ at}
  → ∀{A} → SigTy pt pa A → ∅ ⊢ A → Set where
  base : BApp b (sig2SigTy (signature b)) (builtin b / refl )
  step : ∀{A B}{tn}
    → {pt : tn ∔ 0 ≣ fv (signature b)} 
    → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
    → {σB : SigTy pt (bubble pa) B}
    → {t : ∅ ⊢ A ⇒ B} → BApp b (A B⇒ σB) t
    → {u : ∅ ⊢ A} → Value u → BApp b σB (t · u)
  step⋆ : ∀{C}{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
    → ∀{tn tm} {pt : tn ∔ (suc tm) ≣ fv (signature b)} 
    → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
    → {σB : SigTy (bubble pt) pa B}
    → {t : ∅ ⊢ Π B} → BApp b (sucΠ σB) t
    → {A : ∅ ⊢Nf⋆ K}
    → (q : C ≡ B [ A ]Nf)
    → {σC : SigTy (bubble pt) pa C}
    → BApp b σC (t ·⋆ A / q)

data Value where
  V-ƛ : {A B : ∅ ⊢Nf⋆ *}
    → (M : ∅ , A ⊢ B)
      ---------------------------
    → Value (ƛ M)

  V-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
    → (M : ∅ ,⋆ K ⊢ B)
      ----------------
    → Value (Λ M)

  V-wrap : ∀{K}
   → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {B : ∅ ⊢Nf⋆ K}
   → {M : ∅ ⊢  _}
   → Value M
   → Value (wrap A B M)

  V-con :  ∀{A : ∅ ⊢Nf⋆ ♯}
    → (x : ⟦ A ⟧) 
    → Value (con {A = A} x refl)

  V-I⇒ : ∀ b {A B}{tn}
       → {pt : tn ∔ 0 ≣ fv (signature b)} 
       → ∀{an am}{pa : an ∔ (suc am) ≣ args♯ (signature b)}
       → {σB : SigTy pt (bubble pa) B}
       → {t : ∅ ⊢ A ⇒ B}
       → BApp b (A B⇒ σB) t
       → Value t
  V-IΠ : ∀ b {K}{A : ∅ ,⋆ K ⊢Nf⋆ *}
       → ∀{tn tm} {pt : tn ∔ (suc tm) ≣ fv (signature b)} 
       → ∀{an am}{pa : an ∔ suc am ≣ args♯ (signature b)}
       → {σA : SigTy (bubble pt) pa A}
       → {t : ∅ ⊢ Π A}
       → BApp b (sucΠ σA) t
       → Value t
  V-constr : ∀{n}(e : Fin n) 
          → (TSS : Vec (List ( ∅ ⊢Nf⋆ *)) n )
          → ∀{XS} → (p : XS ≡ Vec.lookup TSS e)
          → ∀{YS} → (q : YS ≡ [] <>< XS)
          → {ts : IBwd (∅ ⊢_) YS}
          → (vs : VList ts)
          → ∀ {ts' : IList (∅ ⊢_) XS} → (IBwd2IList (lemma<>1' _ _ q) ts ≡ ts')
          → Value (constr e TSS p ts')

red2cekVal : ∀{A}{L : ∅ ⊢ A} → Value L → CEK.Value A
red2cekBApp : ∀{b}
   {tn tm tt}{pt : tn ∔ tm ≣ tt}
   {an am at}{pa : an ∔ am ≣ at}
   {A}{L : ∅ ⊢ A}
   {σA : SigTy pt pa A}
  → BApp b σA L → CEK.BApp b A σA

red2cekBApp (base) = CEK.base
red2cekBApp (step x x₁) = (red2cekBApp x) CEK.$ (red2cekVal x₁)
red2cekBApp (step⋆ x refl) = (red2cekBApp x) CEK.$$ refl

red2cekVal-VList : ∀{TS}{ts : IBwd (_⊢_ ∅) TS} →  (vs : VList ts) → CEK.VList TS
red2cekVal-VList [] = []
red2cekVal-VList (vs :< x) = (red2cekVal-VList vs) :< (red2cekVal x)

red2cekVal (V-ƛ M) = CEK.V-ƛ M CEK.[]
red2cekVal (V-Λ M) = CEK.V-Λ M CEK.[]
red2cekVal (V-wrap V) = CEK.V-wrap (red2cekVal V)
red2cekVal (V-con {A} cn) = CEK.V-con cn
red2cekVal (V-I⇒ b x) = CEK.V-I⇒ b (red2cekBApp x)
red2cekVal (V-IΠ b x) = CEK.V-IΠ b (red2cekBApp x)
red2cekVal (V-constr e TSS refl refl vs refl) = CEK.V-constr e TSS (red2cekVal-VList vs) refl

BUILTIN' : ∀ b {A}{t : ∅ ⊢ A}
  → ∀{tn} → {pt : tn ∔ 0 ≣ fv (signature b)}
  → ∀{an} → {pa : an ∔ 0 ≣ args♯ (signature b)}
  → {σA : SigTy pt pa A}
  → BApp b σA t
  → ∅ ⊢ A
BUILTIN' b bt = CEK.BUILTIN' b (red2cekBApp bt) 
```

```
data Error :  ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} → Γ ⊢ A → Set where
  -- an actual error term
  E-error : ∀{Φ Γ }{A : Φ ⊢Nf⋆ *} → Error {Γ = Γ} (error {Φ} A)
```

## Intrinsically Type Preserving Reduction

### Frames

Frames used by the CC and the CK machine, and their plugging function.

```
data Frame : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  -·_     : {A B : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → Frame B (A ⇒ B)
  -·v     : ∀{A B : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A} → Value t → Frame B (A ⇒ B)
  _·-     : {A B : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A ⇒ B} → Value t → Frame B A
  -·⋆     : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}(A : ∅ ⊢Nf⋆ K) → Frame (B [ A ]Nf) (Π B)

  wrap-   : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (μ A B) (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B))
  unwrap- : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}
    → Frame (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) (μ A B)
  constr- : ∀{n VS H TS} 
          → (i : Fin n) 
          → (TSS : Vec _ n)  
          → ∀ {XS} → (XS ≡ Vec.lookup TSS i)
          → {tidx : XS ≣ VS <>> (H ∷ TS)} → {tvs : IBwd (∅ ⊢_) VS} → VList tvs → ConstrArgs ∅ TS
          → Frame (SOP TSS) H
  case-   : ∀{A n}{TSS : Vec _ n} → Cases ∅ A TSS → Frame A (SOP TSS) 

_[_]ᶠ : ∀{A B : ∅ ⊢Nf⋆ *} → Frame B A → ∅ ⊢ A → ∅ ⊢ B
(-· M')          [ L ]ᶠ = L · M'
(-·v V)          [ L ]ᶠ = L · deval V
(V ·-)           [ L ]ᶠ = deval V · L
-·⋆ A            [ L ]ᶠ = L ·⋆ A / refl
wrap-            [ L ]ᶠ = wrap _ _ L
unwrap-          [ L ]ᶠ = unwrap L refl
constr- i TSS refl {tidx} {tvs} _ ts [ L ]ᶠ = constr i TSS (sym (lem-≣-<>> tidx)) (tvs <>>I (L ∷ ts))
case- cs         [ L ]ᶠ = case L cs
```

## Evaluation Contexts

```
data EC : (T : ∅ ⊢Nf⋆ *) → (H : ∅ ⊢Nf⋆ *) → Set where
  []   : {A : ∅ ⊢Nf⋆ *} → EC A A
  _l·_ : {A B C : ∅ ⊢Nf⋆ *} → EC (A ⇒ B) C → (t : ∅ ⊢ A) → EC B C
  _·r_ : {A B C : ∅ ⊢Nf⋆ *}{t : ∅ ⊢ A ⇒ B} → Value t → EC A C → EC B C
  _·⋆_/_ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{C}{X}
    → EC (Π B) C → (A : ∅ ⊢Nf⋆ K) → X ≡ B [ A ]Nf → EC X C
  wrap : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}
    → EC (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) C
    → EC (μ A B) C
  unwrap_/_ : ∀{K}{A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}{B : ∅ ⊢Nf⋆ K}{C}{X}
    → EC (μ A B) C
    → X ≡ (nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)) 
    → EC X C
  constr : ∀{n VS H TS C} 
          → (i : Fin n) 
          → (TSS : Vec _ n)  
          → ∀ {XS} → (XS ≡ Vec.lookup TSS i)
          → {tidx : XS ≣ VS <>> (H ∷ TS)} 
          → {tvs : IBwd (∅ ⊢_) VS} → VList tvs → ConstrArgs ∅ TS
          → EC H C
          → EC (SOP TSS) C
  case   :  ∀{A C n}{TSS : Vec _ n} → Cases ∅ A TSS → EC (SOP TSS) C → EC A C

-- Plugging of evaluation contexts
_[_]ᴱ : ∀{A B : ∅ ⊢Nf⋆ *} → EC B A → ∅ ⊢ A → ∅ ⊢ B
[]       [ L ]ᴱ = L
(E l· B) [ L ]ᴱ = E [ L ]ᴱ · B
(V ·r E) [ L ]ᴱ = deval V · E [ L ]ᴱ
(E ·⋆ A / q) [ L ]ᴱ = E [ L ]ᴱ ·⋆ A / q
(wrap   E) [ L ]ᴱ = wrap _ _ (E [ L ]ᴱ)
(unwrap E / q) [ L ]ᴱ = unwrap (E [ L ]ᴱ) q
constr i TSS p {idx} {tvs} vs ts E [ L ]ᴱ = constr i TSS (trans (sym (lem-≣-<>> idx)) p) (tvs <>>I (E [ L ]ᴱ ∷ ts))
case cs E [ L ]ᴱ = case (E [ L ]ᴱ) cs
```

## Evaluation Relation

```
applyCase : ∀ {A : ∅ ⊢Nf⋆ *} 
              {ts : List (∅ ⊢Nf⋆ *)}
              (f : ∅ ⊢ mkCaseType A ts)
           →  (cs : ConstrArgs ∅ ts)
           → ∅ ⊢ A
applyCase f [] = f
applyCase f (x ∷ cs) = applyCase (f · x) cs            

infix 2 _—→⋆_

data _—→⋆_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where
  β-ƛ : {A B : ∅ ⊢Nf⋆ *}{N : ∅ , A ⊢ B} {V : ∅ ⊢ A}
    → Value V
      -------------------
    → (ƛ N) · V —→⋆ N [ V ]

  β-Λ : ∀ {K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{N : ∅ ,⋆ K ⊢ B}{A}{C}
    → (p : C ≡ _)
      -------------------
    → (Λ N) ·⋆ A / p —→⋆ substEq (∅ ⊢_) (sym p) (N [ A ]⋆)

  β-wrap : ∀{K}
    → {A : ∅ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : ∅ ⊢Nf⋆ K}
    → {C : _}
    → {M : ∅ ⊢ _}
    → Value M
    → (p : C ≡ _)
    → unwrap (wrap A B M) p —→⋆ substEq (∅ ⊢_) (sym p) M

  β-builtin : ∀{A B}{tn}
      (b : Builtin)
    → (t : ∅ ⊢ A ⇒ B)
    → {pt : tn ∔ 0 ≣ fv (signature b)} 
    → ∀{an} → {pa : an ∔ 1 ≣  args♯ (signature b)}
    → {σB : SigTy pt (bubble pa) B}
    → (bt : BApp b (A B⇒ σB) t) -- one left
    → (u : ∅ ⊢ A)
    → (vu : Value u)
      -----------------------------
    → t · u —→⋆ BUILTIN' b (step bt vu)

  β-case : ∀{n}{A : ∅ ⊢Nf⋆ *}
    → (e : Fin n)
    → (TSS : Vec (List (∅ ⊢Nf⋆ *)) n)
    → ∀{YS} → (q : YS ≡ [] <>< Vec.lookup TSS e)
    → {ts : IBwd (∅ ⊢_) YS}
    → (vs : VList ts)
    → ∀ {ts' : IList (∅ ⊢_) (Vec.lookup TSS e)} → (IBwd2IList (lemma<>1' _ _ q) ts ≡ ts')
    → (cases : Cases ∅ A TSS)
    → case (constr e TSS refl ts') cases —→⋆ applyCase (lookupCase e cases) ts'
-- -}
```

```
infix 2 _—→_

data _—→_ : {A : ∅ ⊢Nf⋆ *} → (∅ ⊢ A) → (∅ ⊢ A) → Set where

  ruleEC : ∀{A B}{L L' : ∅ ⊢ B}
         → (E : EC A B)
         → L —→⋆ L'
         → ∀{M M' : ∅ ⊢ A}
         → M ≡ E [ L ]ᴱ
         → M' ≡ E [ L' ]ᴱ
           ----
         → M —→ M'

  ruleErr : ∀{A B}
          → (E : EC B A)
          → ∀{M : ∅ ⊢ B}
          → M ≡ E [ error A ]ᴱ
            ------------------------
          → M —→ error B
```

### Reflexive-transitive closure of evaluation relation

```
data _—↠_ : {A : ∅ ⊢Nf⋆ *} → ∅ ⊢ A → ∅ ⊢ A → Set
  where

  refl—↠ : ∀{A}{M : ∅ ⊢ A}
      --------
    → M —↠ M

  trans—↠ : {A : ∅ ⊢Nf⋆ *}{M  M' M'' : ∅ ⊢ A}
    → M —→ M'
    → M' —↠ M''
      ---------
    → M —↠ M''
```

A smart constructor that looks at the arity and then puts on the
right constructor

```
V-I :  ∀ (b : Builtin) {A : ∅ ⊢Nf⋆ *}
       → ∀{tn tm} {pt : tn ∔ tm ≣ fv (signature b)}
       → ∀{an am} {pa : an ∔ suc am ≣ args♯ (signature b)}
       → {σA : SigTy pt pa A}
       → {t : ∅ ⊢ A}
       → BApp b σA t
       → Value t
V-I b {tm = zero} {σA = A B⇒ σA} bt = V-I⇒ b bt
V-I b {tm = suc tm} {σA = sucΠ σA} bt = V-IΠ b bt
```

For each builtin, return the value corresponding to the completely unapplied builtin

```
ival : ∀ b → Value (builtin b / refl)
ival b = V-I b base
-- -}
```
 