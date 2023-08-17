

```
module Utils.Reflection where
```

## Imports

```
open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Show using (show)
open import Data.List using (List;[];_∷_;_++_;map;[_];length)
open import Data.String using () renaming (_++_ to _+++_)
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
constructors : Definition → Names
constructors (data-type pars cs) = cs
constructors _ = []

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
