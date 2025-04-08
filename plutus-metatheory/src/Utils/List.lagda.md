---
title: Utils.List
layout: page
---
```
module Utils.List where
```

This module contains definitions, functions and properties for different kinds lists, such as
backwards lists, indexed lists, and lists indexed over indexed lists.

## Imports

```
open import Data.Nat using (ℕ;zero;suc)
open import Data.List using (List;[];_∷_;_++_;map;foldr;length;head) public
open import Data.List.Properties using (foldr-++;++-cancelʳ;∷-injective)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;cong;trans;subst;subst-subst)
open import Data.Empty using (⊥;⊥-elim)
open import Data.Integer using (ℤ; pos)
open import Data.Product using (Σ;_×_;_,_;proj₂)
open import Relation.Nullary using (¬_)

open import Utils using (≡-subst-removable)
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

Some cancellation lemmas

```
<><-cancelʳ : ∀{A : Set} (bs bs' : Bwd A) xs → bs <>< xs ≡ bs' <>< xs → bs ≡ bs'
<><-cancelʳ bs bs' [] p = p
<><-cancelʳ bs bs' (x ∷ xs) p with <><-cancelʳ (bs :< x) (bs' :< x) xs p
... | refl = refl

<>>[]-cancelʳ : ∀{A : Set} (bs bs' : Bwd A) → bs <>> [] ≡ bs' <>> [] → bs ≡ bs'
<>>[]-cancelʳ bs bs' p = trans (sym (lemma<>2' bs (bs' <>> []) p)) (lemma<>2 bs' [])

<>>-cancelʳ : ∀{A : Set} (bs bs' : Bwd A) xs → bs <>> xs ≡ bs' <>> xs → bs ≡ bs'
<>>-cancelʳ bs bs' xs p = <>>[]-cancelʳ bs bs'
        (++-cancelʳ xs (bs <>> []) (bs' <>> [])
          (trans
            (sym (lemma-<>>-++ bs [] xs))
            (trans p (lemma-<>>-++ bs' [] xs))
          )
        )

<>>-cancelˡ : ∀{A : Set} (bs : Bwd A) xs xs' → bs <>> xs ≡ bs <>> xs' → xs ≡ xs'
<>>-cancelˡ [] xs xs' p = p
<>>-cancelˡ (bs :< x) xs xs' p with <>>-cancelˡ bs (x ∷ xs) (x ∷ xs') p
... | refl = refl
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

-- Injectivity of cons
∷-injectiveI : ∀ {A : Set}{B : A → Set}{t : A}{ts ts' : List A}
    {X Y : B t}{Xs : IList B ts}{Ys : IList B ts'}
    → (p : t ∷ ts' ≡ t ∷ ts)
    → _≡_ {_} {IList B (t ∷ ts)} (X ∷ Xs)  (subst (IList B) p (Y ∷ Ys))
    → X ≡ Y × Xs ≡ subst (IList B) (proj₂ (∷-injective p)) Ys
∷-injectiveI refl refl = refl , refl
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

lemma<>I2' : ∀{A}{B : A → Set}{xs : Bwd A}{ys : List A}(ixs : IBwd B xs)(iys : IList B ys)
                  → ([] <><I (ixs <>>I iys)) ≡ subst (IBwd B) (sym (lemma<>2 xs ys)) (ixs <><I iys)
lemma<>I2' [] iys = refl
lemma<>I2' (ixs :< ix) iys = lemma<>I2' ixs (ix ∷ iys)

IBwd2IList' : ∀{A}{B : A → Set}{bs}{ts} → (bs ≡ [] <>< ts) → IBwd B bs → IList B ts
IBwd2IList' {ts = ts} p tbs = subst (IList _) (trans (cong (_<>> []) p) (lemma<>1 [] ts)) (tbs <>>I [])

IBwd2IList : ∀{A}{B : A → Set}{bs}{ts} → (bs <>> [] ≡ ts) → IBwd B bs → IList B ts
IBwd2IList p tbs = subst (IList _) p (tbs <>>I [])

IList2IBwd : ∀{A}{B : A → Set}{ts}{bs} → ([] <>< ts ≡ bs) → IList B ts → IBwd B bs
IList2IBwd {ts = ts} p tbs = subst (IBwd _) p ([] <><I tbs)

IBwd<>IList : ∀{A}{B : A → Set}{bs}{ts} → (p : bs <>> [] ≡ ts) → {ibs : IBwd B bs}
            → {its : IList B ts}
            → IBwd2IList p ibs ≡ its
            → ibs ≡ IList2IBwd (lemma<>2' _ _ p) its
IBwd<>IList refl {ibs} refl rewrite lemma<>I2 ibs [] = refl

split :  ∀{A : Set} bs (ts : List A){B : A → Set} → IList B (bs <>> ts) → IBwd B bs × IList B ts
split [] ts vs = [] , vs
split (bs :< x) ts vs with split bs (x ∷ ts) vs
... | ls , (x ∷ rs) = ls :< x , rs

bsplit : ∀{A : Set} bs (ts : List A){B : A → Set} → IBwd B (bs <>< ts) → IBwd B bs × IList B ts
bsplit bs [] vs = vs , []
bsplit bs (x ∷ ts) vs with bsplit (bs :< x) ts vs
... | ls :< x , rs = ls , (x ∷ rs)

inj-IBwd2IList : ∀{A}{B : A → Set}{Bs}{As : List A}{ts ts' : IBwd B Bs}
           → (p : Bs <>> [] ≡ As)
           → IBwd2IList {ts = As} p ts ≡ IBwd2IList p ts'
           → ts ≡ ts'
inj-IBwd2IList refl q = trans (trans (sym (lemma<>I2 _ [])) (cong (IList2IBwd (lemma<>2' _ _ refl)) q)) (lemma<>I2 _ [])
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

unique-≣-<>> : ∀{A : Set}{tot vs}{ts : List A}(p q : tot ≣ vs <>> ts) → p ≡ q
unique-≣-<>> start start = refl
unique-≣-<>> (bubble p) (bubble q) with unique-≣-<>> p q
... | refl = refl

lemma-≣-<>>-refl : ∀{A}(xs : Bwd A)(ys : List A) → (xs <>> ys) ≣ xs <>> ys
lemma-≣-<>>-refl [] ys = start
lemma-≣-<>>-refl (xs :< x) ys = bubble (lemma-≣-<>>-refl xs (x ∷ ys))
```

## Lists indexed by an indexed list

```
data IIList {A : Set}{B : A → Set}(C : ∀{a : A}(b : B a) → Set) : ∀{is} → IList B is → Set where
  [] : IIList C []
  _∷_ : ∀{a as}{i : B a}{is : IList B as} → C i → IIList C is → IIList C (i ∷ is)


data IIBwd {A : Set}{B : A → Set}(C : ∀{a : A}→ B a → Set) : ∀{is} → IBwd B is → Set where
  [] : IIBwd C []
  _:<_ : ∀{a as}{i : B a}{is : IBwd B as} → IIBwd C is → C i → IIBwd C (is :< i)

-- Chip for double indexed lists
_<>>II_ :  ∀{A : Set}{B : A → Set}{C : ∀{a : A}(b : B a) → Set}{bs : Bwd A}{ts : List A}
        {ibs : IBwd B bs}{its : IList B ts}
      → IIBwd C ibs → IIList C its → IIList C (ibs <>>I its)
[] <>>II tls = tls
(tbs :< x) <>>II tls = tbs <>>II (x ∷ tls)

-- Convert an IIBwd into an IIList
IIBwd2IIList : ∀{A}{B : A → Set}{C : ∀{a : A}(b : B a) → Set}{bs}{ts : List A}
               {ibs : IBwd B bs}{its : IList B ts}
             → (p : bs <>> [] ≡ ts)
             → (q : subst (IList B) p (ibs <>>I []) ≡  its)
             → IIBwd C ibs
             → IIList C its
IIBwd2IIList refl refl tbs = tbs <>>II []

-- Split an IIList
splitI : ∀{A : Set}{bs}{ts : List A}{B : A → Set}{C : ∀{a : A}(b : B a) → Set}
           (ibs : IBwd B bs)(its : IList B ts)
        → IIList C (ibs <>>I its) → IIBwd C ibs × IIList C its
splitI [] its xs = [] , xs
splitI (ibs :< x) its xs with splitI ibs (x ∷ its) xs
... | ls , (y ∷ rs) = (ls :< y) , rs

-- Split an IIBwd
bsplitI : ∀{A : Set}{bs}{ts : List A}{B : A → Set}{C : ∀{a : A}(b : B a) → Set}
           (ibs : IBwd B bs)(its : IList B ts)
        → IIBwd C (ibs <><I its) → IIBwd C ibs × IIList C its
bsplitI ibs [] vs = vs , []
bsplitI ibs (x ∷ its) vs with bsplitI (ibs :< x) its vs
... | ls :< x , rs = ls , (x ∷ rs)

-- project from an IIList
proj-IIList : ∀{A : Set}{B : A → Set}{C : ∀{a : A}(b : B a) → Set}
              {a} (b : B a) {Bs}{Fs}
              (bs : IBwd B Bs) (fs : IList B Fs)
             → IIList C (bs <>>I (b ∷ fs))
             → C b
proj-IIList b bs fs xs with splitI bs (b ∷ fs) xs
... | _ , (Cb ∷ _) = Cb

-- project from an IIBwd
proj-IIBwd : ∀{A : Set}{B : A → Set}{C : ∀{a : A}(b : B a) → Set}
              {a} (b : B a) {Bs}{Fs}
              (bs : IBwd B Bs) (fs : IList B Fs)
             → IIBwd C (bs <><I (b ∷ fs))
             → C b
proj-IIBwd b bs fs xs with bsplitI bs (b ∷ fs) xs
... | _ , (Cb ∷ _) = Cb

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

lemma<>I3 : ∀{A}{B : A → Set}{bs : Bwd A}
          → (ibs : IBwd B bs)(iys : IList B (bs <>> []))
          → ibs <>>I [] ≡ iys → subst (IBwd B) (lemma<>2 bs []) ([] <><I iys) ≡ ibs
lemma<>I3 xs ys refl = lemma<>I2 xs []

lem-<><I-subst :  ∀{A : Set}{B : A → Set}{tot tot' : List A}{itot : IList B tot}
      → (p : tot ≡ tot')
      → ([] <><I subst (IList B) p itot) ≡ subst (IBwd B) (cong ([] <><_) p) ([] <><I itot)
lem-<><I-subst refl = refl

lemma-<>>I-++I : ∀{A : Set}{B : A → Set}{bs}{as as' : List A}
        → (ibs : IBwd B bs)(ias : IList B as)(ias' : IList B as')
        →  ibs <>>I (ias ++I ias') ≡  subst (IList B) (sym (lemma-<>>-++ bs as as')) ((ibs <>>I ias) ++I ias')
lemma-<>>I-++I [] ias ias' = refl
lemma-<>>I-++I (ibs :< x) ias ias' = lemma-<>>I-++I ibs (x ∷ ias) ias'
```

Cancellation law for <>>I

```
<>>I[]-cancelʳ : ∀{A : Set}{B : A → Set}{bs : Bwd A}(ibs ibs' : IBwd B bs)
               → ibs <>>I [] ≡ ibs' <>>I [] → ibs ≡ ibs'
<>>I[]-cancelʳ ibs ibs' p = trans (sym (lemma<>I3 ibs (ibs' <>>I []) p)) (lemma<>I2 ibs' [])

<>>I-cancelˡ : ∀{A : Set}{B : A → Set}{bs : Bwd A}{xs}
                (ibs : IBwd B bs)
              → (ixs ixs' : IList B xs)
              → ibs <>>I ixs ≡ ibs <>>I ixs' → ixs ≡ ixs'
<>>I-cancelˡ [] ixs ixs' p = p
<>>I-cancelˡ (ibs :< x) ixs ixs' p with <>>I-cancelˡ ibs (x ∷ ixs) (x ∷ ixs') p
... | refl = refl

```
We may have that Bs <>>I (H :: Fs) ≡ Bs' <>>I (H' :: Fs').
We cannot conclude that Bs ≡ Bs', H ≡ H' and Fs ≡ Fs', because the focus
could be at different places of the same indexed list.
However, if there is a predicate P such that P holds for every element of Bs and Bs',
but ¬(P H) and ¬(P H'), then this determines where the focus is and we may conclude that
Bs ≡ Bs', H ≡ H' and Fs ≡ Fs'.

```
equalbyPredicate++ : ∀{A : Set}
                    (P : A → Set)
                    {bs bs' : List A}{fs fs'}
                    {tot : List A}
                    {h h' : A}
                  → (p : tot ≡ bs ++ (h ∷ fs))
                  → (p' : tot ≡ bs' ++ (h' ∷ fs'))
                  → (IList P bs)
                  → (IList P bs')
                  → (¬Ph : ¬(P h))
                  → (¬Ph' : ¬(P h'))
                  → bs ≡ bs'
equalbyPredicate++ P p p' [] [] ¬Ph ¬Ph' = refl
equalbyPredicate++ P refl refl [] (x ∷ ps') ¬Ph ¬Ph' = ⊥-elim (¬Ph x)
equalbyPredicate++ P refl refl (x ∷ ps) [] ¬Ph ¬Ph' = ⊥-elim (¬Ph' x)
equalbyPredicate++ P {a ∷ as} refl p' (x ∷ ps) (x₁ ∷ ps') ¬Ph ¬Ph' with ∷-injective p'
... | refl , q = cong (a ∷_) (equalbyPredicate++ P {as} refl q ps ps' ¬Ph ¬Ph')


equalbyPredicate : ∀{A : Set}
                    (P : A → Set)
                    {bs bs' : Bwd A}{fs fs'}{tot}
                    {h h' : A}
                  → (p : tot ≡ bs <>> (h ∷ fs))
                  → (p' : tot ≡ bs' <>> (h' ∷ fs'))
                  → (IBwd P bs)
                  → (IBwd P bs')
                  → (¬Ph : ¬(P h))
                  → (¬Ph' : ¬(P h'))
                  → bs ≡ bs'
equalbyPredicate P {bs} {bs'} {fs} {fs'} {tot} {h} {h'} p p' ps ps' ¬Ph ¬Ph' =
    <>>[]-cancelʳ _ _ (equalbyPredicate++ P
                      (trans p (lemma-<>>-++ bs [] (h ∷ fs)))
                      (trans p' (lemma-<>>-++ bs' [] (h' ∷ fs')))
                      (IBwd2IList refl ps)
                      (IBwd2IList refl ps')
                      ¬Ph
                      ¬Ph')

equalbyPredicate++I : ∀{A : Set}{B : A → Set}{bs bs' : List A}{fs fs'}{tot}
                    (TOT : IList B tot)
                    {Bs : IList B bs}{Bs' : IList B bs'}
                    {Fs : IList B fs}{Fs' : IList B fs'}
                    {h h' : A}
                    {H : B h}{H' : B h'}
                  → (P : {a : A} → B a → Set)
                  → (p : tot ≡ bs ++ (h ∷ fs))
                  → (p' : tot ≡ bs' ++ (h' ∷ fs'))
                  → (q : TOT ≡ subst (IList B) (sym p) (Bs ++I (H ∷ Fs)))
                  → (q' : TOT ≡ subst (IList B) (sym p') (Bs' ++I (H' ∷ Fs')))
                  → (ps : IIList P Bs)
                  → (ps' : IIList P Bs')
                  → (¬PH : ¬(P H))
                  → (¬PH' : ¬(P H'))
                  → Σ (bs ≡ bs') (λ { refl →
                    Σ (h ≡ h')   (λ { refl →
                    Σ (fs ≡ fs') (λ { refl → Bs ≡ Bs' }) }) })
equalbyPredicate++I TOT P p p' q q' [] [] ¬PH ¬PH' with ∷-injective (trans (sym p) p')
... | refl , refl = refl , (refl , (refl , refl))
equalbyPredicate++I TOT P refl refl refl refl [] (x ∷ ps') ¬PH ¬PH' = ⊥-elim (¬PH x)
equalbyPredicate++I TOT P refl refl refl refl (x ∷ ps) [] ¬PH ¬PH' = ⊥-elim (¬PH' x)
equalbyPredicate++I TOT P refl p' refl q' (x ∷ ps) (x₁ ∷ ps') ¬PH ¬PH' with ∷-injective p'
... | refl , pt with ∷-injectiveI (sym p') q'
... | refl , qt with equalbyPredicate++I _ P refl pt refl
                                       (trans qt (≡-subst-removable (IList _) (proj₂ (∷-injective (sym p'))) (sym pt) _))
                                        ps ps' ¬PH ¬PH'
... | refl , refl , refl , refl = refl , (refl , (refl , refl))

equalbyPredicateI : ∀{A : Set}{B : A → Set}{bs bs' : Bwd A}{fs fs'}{tot}
                    (TOT : IList B tot)
                    {Bs : IBwd B bs}{Bs' : IBwd B bs'}
                    {Fs : IList B fs}{Fs' : IList B fs'}
                    {h h' : A}
                    {H : B h}{H' : B h'}
                  → (P : {a : A} → B a → Set)
                  → (p : tot ≡ bs <>> (h ∷ fs))
                  → (p' : tot ≡ bs' <>> (h' ∷ fs'))
                  → (q : TOT ≡ subst (IList B) (sym p) (Bs <>>I (H ∷ Fs)))
                  → (q' : TOT ≡ subst (IList B) (sym p') (Bs' <>>I (H' ∷ Fs')))
                  → (ps : IIBwd P Bs)
                  → (ps' : IIBwd P Bs')
                  → (¬PH : ¬(P H))
                  → (¬PH' : ¬(P H'))
                  → Σ (bs ≡ bs') (λ { refl →
                    Σ (h ≡ h')   (λ { refl →
                    Σ (fs ≡ fs') (λ { refl → Bs ≡ Bs' }) }) })
equalbyPredicateI {bs = bs}{bs'}{fs}{fs'}{tot} TOT {Bs} {Bs'} {Fs} {Fs'} {h} {h'} {H} {H'} P refl p' refl q' ps ps' ¬PH ¬PH' with
     equalbyPredicate++I TOT
               P
               (lemma-<>>-++ bs [] (h ∷ fs))
               (trans p' (lemma-<>>-++ bs' [] (h' ∷ fs')))
               ((lemma-<>>I-++I Bs [] (H ∷ Fs)))
               (trans q'
                (trans (cong (subst (IList _) (sym p')) (lemma-<>>I-++I Bs' [] (H' ∷ Fs')))
                 (trans (subst-subst {P = IList _} (sym (lemma-<>>-++ bs' [] (h' ∷ fs'))) {sym p'} {(Bs' <>>I []) ++I (H' ∷ Fs')})
                         (≡-subst-removable (IList _) (trans (sym (lemma-<>>-++ bs' [] (h' ∷ fs'))) (sym p')) (sym (trans p' (lemma-<>>-++ bs' [] (h' ∷ fs')))) _))))
               (IIBwd2IIList refl refl ps)
               (IIBwd2IIList refl refl ps')
               ¬PH
               ¬PH'
... | pbs , snd with <>>[]-cancelʳ bs bs' pbs
equalbyPredicateI TOT {Bs} {Bs'} P p p' q q' ps ps' ¬PH ¬PH'
     | refl , refl , refl , pBs | refl with <>>I[]-cancelʳ Bs Bs' pBs
... | refl = refl , refl , refl , refl
