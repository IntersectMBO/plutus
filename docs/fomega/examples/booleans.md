The `boolean` type may be expressed in Plutus Core as:
```
(all a (type) (fun a (fun a a)))
```
and then for `true` and `false` we choose
```
(abs a (type) (lam x a (lam y a x)))
```
and
```
(abs a (type) (lam x a (lam y a y)))
```
respectively. 
Now, `case` is 
```
(abs b (type)
  (lam x (all a (type) (fun a (fun a a)))
  (lam t b
  (lam f b
      [{x b} t f]))))
``` 

Something more interesting we can do with booleans is negation:
```
(lam x (all a (type) (fun a (fun a a)))
[
 {(abs b (type) (lam x (all a (type) (fun a (fun a a))) 
      (lam t b (lam f b [{x b} t f]))))
  (all a (type) (fun a (fun a a)))}
 x
 (abs a (type) (lam x a (lam y a y)))
 (abs a (type) (lam t a (lam f a t)))
]) 
```


Note that presently, the Plutus Core typechecker assigns an incorrect type to the above definition of `case`, and in turn rejects our definition of negation. Observe that `case` has type `(all b (type) (fun (all a (type) (fun a (fun a a))) (fun b (fun b b))))` as follows:
```
------------------------------------------   -----------------
Γ ⊢ x : (all a (type) (fun a (fun a a)))      Γ ⊢ b :: (type)
--------------------------------------------------------------                -------------
Γ ⊢ {x b} : (fun b (fun b b))                                                   Γ ⊢ t : b
--------------------------------------------------------------------------------------------    -----------
Γ = b :: (type), x : (all a (type) (fun a (fun a a))), t : b, f : b ⊢ [{x b} t] : (fun b b)      Γ ⊢ f : b
------------------------------------------------------------------------------------------------------------
b :: (type), x : (all a (type) (fun a (fun a a))), t : b, f : b ⊢ [{x b} t f] : b
---------------------------------------------------------------------------------------------
b :: (type), x : (all a (type) (fun a (fun a a))), t : b ⊢ (lam f b [{x b} t f]) : (fun b b)
--------------------------------------------------------------------------------------------------------
b :: (type), x : (all a (type) (fun a (fun a a))) ⊢ (lam t b (lam f b [{x b} t f])) : (fun b (fun b b))
--------------------------------------------------------------------------------------------------------------------------------------------------
b :: (type) ⊢ (lam x (all a (type) (fun a (fun a a))) (lam t b (lam f b [{x b} t f]))) : (fun (all a (type) (fun a (fun a a))) (fun b (fun b b)))
---------------------------------------------------------------------------------------------------------------------------------------------------------------------
⊢ (abs b (type) (lam x (all a (type) (fun a (fun a a))) (lam t b (lam f b [{x b} t f])))) : (all b (type) (fun (all a (type) (fun a (fun a a))) (fun b (fun b b))))
```

The Plutus Core Typechecker assigns `case` a different type:
```
>fileType "/home/chad/iohk/plutus_examples/case"
>"(all b (type) (fun (all a (type) (fun b (fun b b))) (fun b (fun b b))))"
```
so I think something is wrong!