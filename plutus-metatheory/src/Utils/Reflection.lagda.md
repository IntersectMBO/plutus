

```
module Utils.Reflection where
```

## Imports

```
open import Data.List using (List;[];_∷_;_++_;map;[_])
open import Data.Unit using (⊤)
open import Data.Bool using (Bool;true;false)
open import Data.Product using (_,_)
open import Agda.Builtin.Reflection
open import Reflection
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (_because_;Reflects;ofʸ;ofⁿ)
```

 Some definitions to help define functions by reflection

```
constructors : Definition → List Name
constructors (data-type pars cs) = cs
constructors _ = []

vra : {A : Set} → A → Arg A
vra = arg (arg-info visible (modality relevant quantity-0))

mk-cls : Name → Clause
mk-cls q = clause [] (vra (con q []) ∷ vra (con q []) ∷ []) (con (quote true)  [])

wildcard : Arg Pattern
wildcard = vra (dot unknown)

absurd-lam : Term
absurd-lam = pat-lam (absurd-clause (("()" , vra unknown) ∷ []) (vra (absurd 0) ∷ []) ∷ []) []

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
... | true  = clause [] (vra (con q1 []) ∷ vra (con q2 []) ∷ []) 
                        (con (quote _because_)  
                             (vra (con (quote true) []) ∷ vra (con (quote ofʸ) [ vra (con (quote refl) []) ]) ∷ []))
... | false = clause [] (vra (con q1 []) ∷ vra (con q2 []) ∷ []) 
                        (con (quote _because_)  
                        (vra (con (quote false) []) ∷ vra (con (quote ofⁿ) [ vra absurd-lam ]) ∷ []))
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
 