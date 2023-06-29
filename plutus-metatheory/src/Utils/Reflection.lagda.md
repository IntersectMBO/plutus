

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

Helpers for recursive datatypes under `List`

   `data Example = ... | Con (List Example)`
 
The idea of declare-List is that given a name of a function `f` that somehow processes things of type A,
it will produce a new declaration of a function `fList`, that processes lists of A.
 Let say that `f` has type 

   f : τ₁ → ... → τₙ → A → B 

Then `declare-List fList f _⊕_ e, given arguments
   
    _⊕_ : B → C → C
    e : C

   should construct a declaration

   fList : τ₁ → ... → τₙ → List A → C
   fList a₁ ... aₙ []       = e 
   fList a₁ ... aₙ (x ∷ xs) = f a₁ ... aₙ x ⊕ fList a₁ ... aₙ xs

 TODO: Later on we should do a dependent version, where the types B and C
  can depend on all the previous arguments.
```
open import Data.Product using (_×_;_,_)

analyzeType : Name → Type → TC (Args Type × Arg Type × Type)
analyzeType f (pi a (abs s ty@(pi _ _))) = do 
             ( args , A , B) ← analyzeType f ty
             return (a ∷ args , A , B)
analyzeType f (pi A (abs s B)) = return ([] , A , B)
analyzeType f _ = typeError (strErr "Expected" ∷ nameErr f ∷ strErr "to be a pi type" ∷ [])

applyList : Arg Type → Arg Type
applyList B = vArg (def (quote List) (hArg (def (quote Agda.Primitive.lzero) [])  ∷ [ B ]))

mkListType : Args Type → Type → Type → Type
mkListType [] B C = pi (applyList (vArg B)) (abs "_" C)
mkListType (x ∷ args) B C = pi x (abs "_" (mkListType args B C))

mkArgs : ∀{ℓ}{A : Set ℓ} → (ArgInfo → ℕ → Type → A) → Args Type → List A → List A
mkArgs fromℕ [] ps = ps
mkArgs fromℕ (arg i x ∷ as) ps = mkArgs fromℕ as (fromℕ i (length ps) x ∷ ps)

define-ListType : ∀{B C : Set} → Name → (B → C → C) → C -> TC Type
define-ListType f _⊕_ e = do 
       τ ← getType f
       ( argsTy , A , B) ← analyzeType f τ
       C ← inferType (quoteTerm e)
       return (mkListType argsTy B C)

define-List : ∀{B C : Set} → Name → Name → (B → C → C) → C -> TC ⊤
define-List fList f _⊕_ e = do 
       τ ← getType f
       ( argsTy , A , B) ← analyzeType f τ
       let argsTel = mkArgs (λ i n x → ("a" +++ show n) , arg i x) argsTy [] 
       let argsPar = mkArgs (λ i n _ → arg i (var n) ) argsTy []
       let n = length argsPar
       let x = var n
       let xs = var (suc n)
       let listTy = "xs" , applyList A
--       let args = mkArgs (λ i n _ → arg i (var 0 [])) argsTy [] 
--       b ← unquoteTC (def f (args ++ [ vArg (var 0 []) ]))
--       c ← unquoteTC (def fList (args ++ [ vArg (var 0 []) ]))
       defineFun fList
             ( clause (argsTel ++ [ listTy ]) 
                      (argsPar ++ [ vArg (con (quote Data.List.List.[]) []) ]) 
                      (quoteTerm e) 
              ∷ [ clause (argsTel ++  ("x" , A) ∷ [ listTy ]) 
                        (argsPar ++ [ vArg (con (quote Data.List.List._∷_) (vArg x ∷ [ vArg xs ])) ])
                        (quoteTerm e) ])    
                        -- (b ⊕ c)) ])
            
declare-List : ∀{B C : Set} → Name → Name → (B → C → C) → C -> TC ⊤
declare-List fList f _⊕_ e = do 
       τ ← getType f
       ( argsTy , A , B) ← analyzeType f τ
       C ← inferType (quoteTerm e)
       let τ′ = mkListType argsTy B C
       let n = length argsTy
       let argsTel = mkArgs (λ i n x → ("a" +++ show n) , arg i x) argsTy [] 
       let argsPar = mkArgs (λ i n _ → arg i (var 0) ) argsTy []
       let x = var 0
       let xs = var 0 --(suc n)
       let args = mkArgs (λ i n _ → arg i (var 0 [])) argsTy [] 
       let listTy = "xs" , applyList A
       b ← unquoteTC (def f (args ++ [ vArg (var 0 []) ]))
       c ← unquoteTC (def fList (args ++ [ vArg (var 0 []) ]))
       declareDef (vArg fList) τ′
       defineFun fList 
             ( clause (argsTel ++ [ listTy ]) 
                      (argsPar ++ [ vArg (con (quote Data.List.List.[]) []) ]) 
                      (quoteTerm e) 
             ∷ [ clause (argsTel ++ [ listTy ]) 
                        (argsPar ++ [ vArg (con (quote Data.List.List._∷_) (vArg x ∷ [ vArg xs ])) ])
                        (quoteTerm (b ⊕ c)) ]
             )

```  

```
{-
module _ where 

       open import Data.List using (sum)

       data Rose (A : Set) : Set where
         node : A → List (Rose A) → Rose A

       size : ∀{A} → Rose A → ℕ 
      
       sizeList : ∀{A} → List (Rose A) → List ℕ 
       unquoteDef sizeList = define-List sizeList (quote size) _∷_ [] 

       size (node _ []) = 1

       {- Termination checking failed
       size (node _ (x ∷ xs)) = suc (sum (map size xs))
       -}
       size (node _ (x ∷ xs)) = suc (sum (sizeList xs))
-- -}
``` 
