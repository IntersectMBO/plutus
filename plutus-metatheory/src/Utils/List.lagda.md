
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

Fish (<><) and chips (<>>) are two operatos to concatenate a backwards list and 
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

lemma<>2 : ∀{A}(xs : Bwd A)(ys : List A) → ([] <>< (xs <>> ys)) ≡ xs <>< ys
lemma<>2 [] ys = refl
lemma<>2 (xs :< x) ys = lemma<>2 xs (x ∷ ys)

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

IBwd2IList : ∀{A}{B : A → Set}{ts}{ts'} → (ts ≡ [] <>< ts') → IBwd B ts → IList B ts'
IBwd2IList {ts' = ts'} p tbs = subst (IList _) (trans (cong (_<>> []) p) (lemma<>1 [] ts')) (tbs <>>I [])
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

no-empty-≣-<>> : ∀{A : Set}{vs}{h : A}{ts} → [] ≣ vs <>> (h ∷ ts) → ⊥
no-empty-≣-<>> (bubble r) = no-empty-≣-<>> r
```
And dissect the ILists 

```
data IDissect {A : Set}(TODO DONE : A → Set){tot : List A}(itot : IList TODO tot) : 
              ∀{bs ts} 
                                      → IBwd DONE bs
                                      → IList TODO ts
                                      → (tot ≣ bs <>> ts) 
                                      → Set where 
     Idissect : ∀{bs}(ibs : IBwd DONE bs){ts}(ils : IList TODO ts) idx 
             → IDissect TODO DONE itot ibs ils idx
```

## Lists indexed by an indexed list 

```
data IIList {A : Set}{B : A → Set}(C : ∀{a : A}(b : B a) → Set) : ∀{is} → IList B is → Set where
  [] : IIList C []
  _∷_ : ∀{a as}{i : B a}{is : IList B as} → C i → IIList C is → IIList C (i ∷ is)

iiGetIdx : ∀{A : Set}{B : A → Set}{C : ∀{a : A}(b : B a) → Set}{is}{ils : IList B is} → IIList C ils → IList B is
iiGetIdx {ils = ils} _ = ils

data IIBwd {A : Set}{B : A → Set}(C : ∀{a : A}→ B a → Set) : ∀{is} → IBwd B is → Set where
  [] : IIBwd C []
  _:<_ : ∀{a as}{i : B a}{is : IBwd B as} → IIBwd C is → C i → IIBwd C (is :< i)
```
 
 Index for IIList zippers

 ```
data _≣T_<>>_ {A : Set}{B : A → Set}{tot}(itot : IList B tot) : 
                                        ∀{bs ts} 
                                      → IBwd B bs
                                      → IList B ts 
                                      → (tot ≣ bs <>> ts) 
                                      → Set where
  start : (itot ≣T [] <>> itot) start
  bubble : ∀{bs}{ibs : IBwd B bs}{t}{it : B t}{ts}{ils : IList B ts}{idx}
         → (itot ≣T ibs <>> (it ∷ ils)) idx
           ------------------------------------------
         → (itot ≣T (ibs :< it) <>> ils) (bubble idx)

getIdx≡T : ∀{A : Set}{B : A → Set}{tot}{itot : IList B tot}{bs ts}
                                      → {ibs : IBwd B bs}
                                      → {ils : IList B ts}
                                      → {idx : tot ≣ bs <>> ts}
                                      → (itot ≣T ibs <>> ils) idx
                                      → tot ≣ bs <>> ts
getIdx≡T {idx = idx} _ = idx                                      

lem-≣T-<>> : ∀{A : Set}{B : A → Set}{tot : List A}{itot : IList B tot}{bs} 
                                {ibs : IBwd B bs}{ls}{ils : IList B ls}  
                                {idx : tot ≣ bs <>> ls}     
                           → (itot ≣T ibs <>> ils) idx 
                           → subst (IList B) (lem-≣-<>> idx) itot ≡ (ibs <>>I ils)
lem-≣T-<>> start = refl
lem-≣T-<>> (bubble x) = lem-≣T-<>> x

lem-≣T-<>>r : ∀{A : Set}{B : A → Set}{tot : List A}{itot : IList B tot}{bs} 
                                {ibs : IBwd B bs}{ls}{ils : IList B ls}  
                                {idx : tot ≣ bs <>> ls}     
                           → (itot ≣T ibs <>> ils) idx 
                           → itot ≡ subst (IList B)  (sym (lem-≣-<>> idx)) (ibs <>>I ils)
lem-≣T-<>>r start = refl
lem-≣T-<>>r (bubble r) = lem-≣T-<>>r r

lem-≣T-<>>' : ∀{A : Set}{B : A → Set}{tot : List A}{itot : IList B tot}{bs} 
                             {ibs : IBwd B bs}{ls}{ils : IList B ls}  
                             (eq : tot ≡ bs <>> ls)
                           → (subst (IList B) eq itot) ≡ ((ibs <>>I ils))
                           → (itot ≣T ibs <>> ils) (lem-≣-<>>' eq) 
lem-≣T-<>>' {ibs = []} refl refl = start
lem-≣T-<>>' {ibs = ibs :< x} refl refl = bubble (lem-≣T-<>>' refl refl)

data IIDissect {A : Set}{B : A → Set}(DONE TODO : ∀{a : A} → B a → Set){tot : List A}{itot : IList B tot}(iitot : IIList TODO itot) : Set where 
     iiDissect :  ∀{bs}{ibs : IBwd B bs}{ls}{ils : IList B ls}{idx : tot ≣ bs <>> ls} 
               (iidx : (itot ≣T ibs <>> ils) idx)
             → (iibs : IIBwd DONE ibs)(iils : IIList TODO ils) 
              -----------------------------------------------------
             → IIDissect DONE TODO iitot
```

The following datatype can be used to process an IList while recording that predicate P holds for its elements.

```
data IIPZipper {A : Set}{B : A → Set}(P : ∀{a : A} → B a → Set){tot : List A}(itot : IList B tot) : Set where 
     iiPZipper :  ∀{bs}{ibs : IBwd B bs}{ls}{idx : tot ≣ bs <>> ls}
             → (iibs : IIBwd P ibs) 
             → (ils : IList B ls)
             → (iidx : (itot ≣T ibs <>> ils) idx)
              -----------------------------------------------------
             → IIPZipper P itot                                   
```


    