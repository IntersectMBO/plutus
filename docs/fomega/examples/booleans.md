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
k