---
title: Utils.Reflection
layout: page
---

```
module Utils.Reflection where
```

## Imports

```
open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Show using (show)
open import Data.List using (List;[];_∷_;_++_;map;[_];length;last)
open import Data.Maybe using (just;nothing)
open import Data.Char using (_≈ᵇ_)
open import Function using (_∘_)
open import Data.String using (String;wordsBy) renaming (_++_ to _+++_)
open import Data.Unit using (⊤)
open import Data.Bool using (Bool;true;false;T?)
open import Data.Product using (_,_)
open import Agda.Builtin.Reflection
open import Reflection
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (_because_;Reflects;ofʸ;ofⁿ)
```

 Some definitions to help define functions by reflection

```
constructors : Definition → Names
constructors (data-type pars cs) = cs
constructors _ = []

names : String → List String
names = wordsBy (T? ∘ (_≈ᵇ '.'))

lastName : String → List String → String 
lastName s xs with last xs 
... | just x = x
... | nothing = s

getLastName : Name → String 
getLastName q = lastName "defconstructorname" (names (showName q)) 


mk-cls : Name → Clause
mk-cls q = clause [] (vArg (con q []) ∷ vArg (con q []) ∷ []) (con (quote true)  [])

wildcard : Arg Pattern
wildcard = vArg (dot unknown)

absurd-lam : Term
absurd-lam = pat-lam (absurd-clause (("()" , vArg unknown) ∷ []) (vArg (absurd 0) ∷ []) ∷ []) []

default-cls : Clause
default-cls = clause [] (wildcard ∷ (wildcard ∷ [])) (con (quote false) [])

map2 : ∀ {a b} {A : Set a} {B : Set b} → (A → A → B) → List A → List B
map2 {A = A} {B = B} f l = map2' f l l
  where
  map2' : (A → A → B) → List A → List A → List B
  map2' f [] _ = []
  map2' f (x ∷ xs) l = map (f x) l ++ map2' f xs l 

mk-DecCls : Name → Name → Clause
mk-DecCls q1 q2 with primQNameEquality q1 q2
... | true  = clause [] (vArg (con q1 []) ∷ vArg (con q2 []) ∷ []) 
                        (con (quote _because_)  
                             (vArg (con (quote true) []) ∷ vArg (con (quote ofʸ) [ vArg (con (quote refl) []) ]) ∷ []))
... | false = clause [] (vArg (con q1 []) ∷ vArg (con q2 []) ∷ []) 
                        (con (quote _because_)  
                        (vArg (con (quote false) []) ∷ vArg (con (quote ofⁿ) [ vArg absurd-lam ]) ∷ []))
```

The function `defEq` helps to define an equality function for datatypes which are simple enumerations.

```
defEq : Name → Name → TC ⊤
defEq T defName = do
       d ← getDefinition T
       let trueClauses = map mk-cls (constructors d)
       defineFun defName (trueClauses ++ (default-cls ∷ []))
```

The function `defDec` helps to define a `DecidableEquality` for datatypes which are simple enumerations.

```
defDec : Name → Name → TC ⊤
defDec T defName = do
       d ← getDefinition T
       let cls = map2 mk-DecCls (constructors d)
       defineFun defName cls
```

The function `defShow` helps to define a show function for datatypes which are simple enumerations.

``` 
mk-Show : Name → Clause
mk-Show q = clause [] (vArg (con q []) ∷ []) 
                      (lit (string (getLastName q))) 

defShow : Name → Name → TC ⊤
defShow T defName = do
       d ← getDefinition T
       let cls = map mk-Show (constructors d)
       defineFun defName cls
 
``` 

Produce a list with all constructors

``` 
mkList : List Term → Term 
mkList [] = con (quote (List.[])) []
mkList (x ∷ xs) = con (quote _∷_) (hArg unknown ∷  hArg unknown ∷ vArg x ∷ vArg (mkList xs) ∷ [])

defListConstructors : Name → Name → TC ⊤
defListConstructors T defName = do
       d ← getDefinition T
       let cls = clause [] [] (mkList (map (λ q → con q []) (constructors d)))
       defineFun defName (cls ∷ [])
```
