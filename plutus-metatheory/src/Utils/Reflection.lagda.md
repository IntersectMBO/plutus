

```
module Utils.Reflection where
```

## Imports

```
open import Data.List using (List;[];_∷_;_++_;map)
open import Data.Unit using (⊤)
open import Data.Bool using (Bool;true;false)
open import Agda.Builtin.Reflection
open import Reflection

-- Reflection machinery

constructors : Definition → List Name
constructors (data-type pars cs) = cs
constructors _ = []

vra : {A : Set} → A → Arg A
vra = arg (arg-info visible (modality relevant quantity-0))

mk-cls : Name → Clause
mk-cls q = clause [] (vra (con q []) ∷ vra (con q []) ∷ []) (con (quote true)  [])

wildcard : Arg Pattern
wildcard = vra (dot unknown)

default-cls : Clause
default-cls = clause [] (wildcard ∷ (wildcard ∷ [])) (con (quote false) [])

defEq : Name → Name → TC ⊤
defEq T defName = do
       d ← getDefinition T
       let trueClauses = map mk-cls (constructors d)
       defineFun defName (trueClauses ++ (default-cls ∷ []))

