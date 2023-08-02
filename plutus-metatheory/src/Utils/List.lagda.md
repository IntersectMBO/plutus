
```
module Utils.List where
```

This module contains definitions, functions and properties for different kinds lists, such as
backwards lists, indexed lists, and lists indexed over indexed lists.

## Imports

```
open import Data.Nat using (ℕ;zero;suc)
open import Data.List using (List;[];_∷_;_++_;map;foldr;length) public
open import Data.List.Properties using (foldr-++)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;cong;trans;subst)
open import Data.Empty using (⊥) 
```

## Backward Lists

```
data Bwd (A : Set) : Set where
  [] : Bwd A
  _:<_ : Bwd A → A → Bwd A

infixl 5 _:<_

bwd-length : ∀{A} → Bwd A → ℕ
bwd-length [] = 0
bwd-length (az :< a) = suc (bwd-length az)

bwd-foldr : ∀{A B : Set} → (A → B → B) → B → Bwd A → B 
bwd-foldr f e [] = e
bwd-foldr f e (bs :< x) = bwd-foldr f (f x e) bs
```

### Fish and Chips

Fish (<><) and chips (<>>) are two operators to concatenate a backwards list and 
a list together, either by consing every snoc and obtaining a list, or by 
snoc-ing every cons and obtaining a backwards list.

```
_<>>_ : ∀{A} → Bwd A → List A → List A
[] <>> as = as
(az :< a) <>> as = az <>> (a ∷ as)

_<><_ : ∀{A} → Bwd A → List A → Bwd A
az <>< []       = az
az <>< (a ∷ as) = (az :< a) <>< as
```

Snoc for lists and cons for backwards lists.

```
_:<L_ : ∀{A : Set} → List A → A → List A
as :<L a = as ++ (a ∷ [])

_∷B_ : ∀{A : Set} → A → Bwd A → Bwd A
a ∷B []          = [] :< a
a ∷B (as' :< a') = (a ∷B as') :< a' 
```

Useful lemmas

```
lemma<>1 : ∀{A}(xs : Bwd A)(ys : List A) → (xs <>< ys) <>> [] ≡ xs <>> ys
lemma<>1 xs []       = refl
lemma<>1 xs (x ∷ ys) = lemma<>1 (xs :< x) ys

lemma<>1' : ∀{A}(xs : Bwd A)(ys : List A) → xs ≡ [] <>< ys → xs <>> [] ≡ ys
lemma<>1' xs ys refl = lemma<>1 [] ys

lemma<>2 : ∀{A}(xs : Bwd A)(ys : List A) → ([] <>< (xs <>> ys)) ≡ xs <>< ys
lemma<>2 [] ys = refl
lemma<>2 (xs :< x) ys = lemma<>2 xs (x ∷ ys)

lemma<>2' : ∀{A}(xs : Bwd A)(ys : List A) → xs <>> [] ≡ ys → [] <>< ys ≡ xs
lemma<>2' xs ys refl = lemma<>2 xs []

lemma-<>>-++ : ∀{A : Set} bs (as as' : List A) →  bs <>> (as ++ as') ≡ (bs <>> as) ++ as'
lemma-<>>-++ [] as as' = refl
lemma-<>>-++ (bs :< x) as as' = lemma-<>>-++ bs (x ∷ as) as'

lemma-bwd-foldr : ∀{A B}(f : A → B → B)(e : B)(bs : Bwd A) → foldr f e (bs <>> []) ≡ bwd-foldr f e bs
lemma-bwd-foldr f e [] = refl
lemma-bwd-foldr f e (bs :< b) = trans (trans ((cong (foldr f e) (lemma-<>>-++ bs [] (b ∷ [])))) 
                                             (foldr-++ f e (bs <>> []) (b ∷ []))) 
                                      (lemma-bwd-foldr f (f b e) bs)
```

## Indexed Lists

Indexed lists `IList` are lists of elements of an indexed set.
They are indexed by the list of all indices which index its elements.

```
data IList {A : Set}(B : A → Set) : List A → Set where
  [] : IList B []
  _∷_ : ∀{ty ts} → B ty → IList B ts →  IList B (ty ∷ ts)

-- Concatenation for Indexed Lists
_++I_ : ∀{A : Set}{B : A → Set}{ts ts' : List A} 
      → IList B ts → IList B ts' → IList B (ts ++ ts')
[] ++I bs = bs
(x ∷ as) ++I bs = x ∷ (as ++I bs)

lengthT : ∀{A : Set}{ts : List A}{B : A → Set} → IList B ts → ℕ 
lengthT {ts = ts} _ = length ts 

iGetIdx : ∀{A : Set}{ts : List A}{B : A → Set} → IList B ts → List A
iGetIdx {ts = ts} ils = ts

-- snoc for Indexed Lists.
_:<I_ : ∀{A : Set}{B : A → Set}{t}{ts : List A} → IList B ts → B t → IList B (ts :<L t) 
as :<I a = as ++I (a ∷ [])
```

## Backwards Indexed Lists

```
data IBwd {A : Set}(B : A → Set) : Bwd A → Set where
  [] : IBwd B []
  _:<_ : ∀{ty ts}  → IBwd B ts → B ty → IBwd B (ts :< ty)

-- Chip for indexed lists
_<>>I_ :  ∀{A : Set}{B : A → Set}{bs : Bwd A}{ts : List A} 
      → IBwd B bs → IList B ts → IList B (bs <>> ts)
[] <>>I tls = tls
(tbs :< x) <>>I tls = tbs <>>I (x ∷ tls)

_<><I_ :  ∀{A : Set}{B : A → Set}{bs : Bwd A}{ts : List A} 
      → IBwd B bs → IList B ts → IBwd B (bs <>< ts)
ibs <><I [] = ibs
ibs <><I (x ∷ its) = (ibs :< x) <><I its

lemma<>I1 : ∀{A}{B : A → Set}{xs : Bwd A}{ys : List A} → (ixs : IBwd B xs) → (iys : IList B ys) 
                  → (subst (IList B) (lemma<>1 xs ys) ((ixs <><I iys) <>>I [])) ≡ ixs <>>I iys
lemma<>I1 ixs [] = refl
lemma<>I1 ixs (iy ∷ iys) = lemma<>I1 (ixs :< iy) iys

lemma<>I2 : ∀{A}{B : A → Set}{xs : Bwd A}{ys : List A}(ixs : IBwd B xs)(iys : IList B ys) 
                  → subst (IBwd B) (lemma<>2 xs ys) ([] <><I (ixs <>>I iys)) ≡ ixs <><I iys
lemma<>I2 [] iys = refl
lemma<>I2 (ixs :< ix) iys = lemma<>I2 ixs (ix ∷ iys)

IBwd2IList : ∀{A}{B : A → Set}{bs}{ts} → (bs <>> [] ≡ ts) → IBwd B bs → IList B ts
IBwd2IList p tbs = subst (IList _) p (tbs <>>I [])
```

## A type for Zipper indexes

The following datatype allow us to index zippers of indexed lists.

```
data _≣_<>>_ {A : Set} : (as : List A) → Bwd A → List A → Set where
  start : ∀{as} → as ≣ [] <>> as
  bubble : ∀{as}{vs : Bwd A}{t}{ts : List A} 
         → as ≣ vs <>> (t ∷ ts)
           ---------------------------
         → as ≣ (vs :< t) <>> ts 


lem-≣-<>> : ∀{A : Set}{tot vs}{ts : List A} → tot ≣ vs <>> ts → tot ≡ vs <>> ts
lem-≣-<>> start = refl
lem-≣-<>> (bubble x) = lem-≣-<>> x

lem-≣-<>>' : ∀{A : Set}{tot vs}{ts : List A} → tot ≡ vs <>> ts → tot ≣ vs <>> ts
lem-≣-<>>' {vs = []} refl = start
lem-≣-<>>' {vs = vs :< x}{ts} refl = bubble (lem-≣-<>>' refl)

done-≣-<>> : ∀{A : Set}{tot : List A} → tot ≣ ([] <>< tot) <>> []
done-≣-<>> = lem-≣-<>>' (sym (lemma<>1 [] _))

no-empty-≣-<>> : ∀{A : Set}{vs}{h : A}{ts} → [] ≣ vs <>> (h ∷ ts) → ⊥
no-empty-≣-<>> (bubble r) = no-empty-≣-<>> r
```

## Lists indexed by an indexed list 

```
data IIList {A : Set}{B : A → Set}(C : ∀{a : A}(b : B a) → Set) : ∀{is} → IList B is → Set where
  [] : IIList C []
  _∷_ : ∀{a as}{i : B a}{is : IList B as} → C i → IIList C is → IIList C (i ∷ is)

data IIBwd {A : Set}{B : A → Set}(C : ∀{a : A}→ B a → Set) : ∀{is} → IBwd B is → Set where
  [] : IIBwd C []
  _:<_ : ∀{a as}{i : B a}{is : IBwd B as} → IIBwd C is → C i → IIBwd C (is :< i)
```
 
 Index for IIList zippers

 ```
data _≣I_<>>_ {A : Set}{B : A → Set}{tot}(itot : IList B tot) : 
                                        ∀{bs ts} 
                                      → IBwd B bs
                                      → IList B ts 
                                      → (tot ≣ bs <>> ts) 
                                      → Set where
  start : (itot ≣I [] <>> itot) start
  bubble : ∀{bs}{ibs : IBwd B bs}{t}{it : B t}{ts}{ils : IList B ts}{idx}
         → (itot ≣I ibs <>> (it ∷ ils)) idx
           ------------------------------------------
         → (itot ≣I (ibs :< it) <>> ils) (bubble idx)

lem-≣I-<>>1 : ∀{A : Set}{B : A → Set}{tot : List A}{itot : IList B tot}{bs} 
                                {ibs : IBwd B bs}{ls}{ils : IList B ls}  
                                {idx : tot ≣ bs <>> ls}     
                           → (itot ≣I ibs <>> ils) idx 
                           → subst (IList B) (lem-≣-<>> idx) itot ≡ (ibs <>>I ils)
lem-≣I-<>>1 start = refl
lem-≣I-<>>1 (bubble x) = lem-≣I-<>>1 x

lem-≣I-<>>1' : ∀{A : Set}{B : A → Set}{tot : List A}{itot : IList B tot}{bs} 
                                {ibs : IBwd B bs}{ls}{ils : IList B ls}  
                                {idx : tot ≣ bs <>> ls}     
                           → (itot ≣I ibs <>> ils) idx 
                           → itot ≡ subst (IList B)  (sym (lem-≣-<>> idx)) (ibs <>>I ils)
lem-≣I-<>>1' start = refl
lem-≣I-<>>1' (bubble r) = lem-≣I-<>>1' r

lem-≣I-<>>2 : ∀{A : Set}{B : A → Set}{tot : List A}{itot : IList B tot}{bs} 
                             {ibs : IBwd B bs}{ls}{ils : IList B ls}  
                             (eq : bs <>> ls ≡ tot)
                           → itot ≡ subst (IList B) eq ((ibs <>>I ils))
                           → (itot ≣I ibs <>> ils) (lem-≣-<>>' (sym eq)) 
lem-≣I-<>>2 {ibs = []} refl refl = start
lem-≣I-<>>2 {ibs = ibs :< x} refl refl = bubble (lem-≣I-<>>2 refl refl)

lem-≣I-<>>2' : ∀{A : Set}{B : A → Set}{tot : List A}{itot : IList B tot}{bs} 
                             {ibs : IBwd B bs}{ls}{ils : IList B ls}  
                             (eq : tot ≡ bs <>> ls)
                           → (subst (IList B) eq itot) ≡ ((ibs <>>I ils))
                           → (itot ≣I ibs <>> ils) (lem-≣-<>>' eq) 
lem-≣I-<>>2' {ibs = []} refl refl = start
lem-≣I-<>>2' {ibs = ibs :< x} refl refl = bubble (lem-≣I-<>>2' refl refl)

done-≣I-<>> : ∀{A : Set}{B : A → Set}{tot : List A}(itot : IList B tot) → (itot ≣I ([] <><I itot) <>> []) done-≣-<>>
done-≣I-<>> itot = lem-≣I-<>>2 (lemma<>1 [] _) (sym (lemma<>I1 [] itot))
```


    