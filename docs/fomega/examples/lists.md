The `list` type may be expressed in Plutus Core as:
```
(lam a (type) (fix list (all r (type) (fun (fun r (fun (fun a list) r)) r))))
```
with `nil` given by:
```
(abs a (type) (wrap list (all r (type) (fun (fun r (fun (fun a list) r)) r))
                (lam nil r (lam cons (fun a (fix list (all r (type) (fun (fun r (fun (a list) r)) r))))
		  nil))))
```
and `cons` given by:
```
(abs a (type) (lam x a (lam xs (fix list (all r (type) (fun (fun r (fun (a list) r)) r)))
  (wrap list (all r (type) (fun (fun r (fun (fun a list) r)) r))
    (abs r (type) (lam nil r (lam cons (fun (fun a (fix list (all r (type (fun (fun r (fun (fun a list) r)) r))))) r)
      ([cons x xs]))))))))
```


We can define `head`:
```
(abs a (type) (lam xs (fix list (all r (type) (fun (fun r (fun (fun a list) r)) r)))
  [{(unwrap xs) a} (error a) (lam head a (lam tail (fix list (all r (type) (fun (fun r (fun (fun a list) r)) r))) head))]))
```
and `tail`:
```
(abs a (type) (lam xs (fix list (all r (type) (fun (fun r (fun (fun a list) r)) r)))
  [{(unwrap xs) (fix list (all r (type) (fun (fun r (fun (fun a list) r)) r)))}
   (error (fix list (all r (type) (fun (fun r (fun (fun a list) r)) r))))
   (lam head a (lam tail (fix list (all r (type) (fun (fun r (fun (fun a list) r)) r))) tail))]))
```
without too much trouble.

`fold` is tricky, but making use of the existing notes we eventually arrive at:
```
[ (unwrap (wrap (fun t (all a (type) (all b (type) (fun (fun (fun b (fun (fun a b) b)) (fix list (all r (type) (fun (fun r (fun (fun a list) r)) r))) b)))))
  (lam y (fix t (fun t (all a (type) (all b (type) (fun (fun (fun (fun a b) b) (fix list (all r (type) (fun (fun r (fun (fun a list) r)) r))) b))))))
    (abs a (type) (abs b (type) (lam fnil b (lam fcons (fun (fun a b) b) (lam xs (fix list (all r (type) (fun (fun r (fun (a list) r)) r)))
      [ {(unwrap xs) b} fnil (lam z a (lam zs (fix list (all r (fun (fun r (fun (a list) r)) r))) [ fcons a [{[(unwrap y) y] a b} fnil fcons zs]]))]))))))))
  (wrap (fun t (all a (type) (all b (type) (fun (fun (fun b (fun (fun a b) b)) (fix list (all r (type) (fun (fun r (fun (fun a list) r)) r))) b)))))
    (lam y (fix t (fun t (all a (type) (all b (type) (fun (fun (fun (fun a b) b) (fix list (all r (type) (fun (fun r (fun (fun a list) r)) r))) b))))))
      (abs a (type) (abs b (type) (lam fnil b (lam fcons (fun (fun a b) b) (lam xs (fix list (all r (type) (fun (fun r (fun (a list) r)) r)))
        [ {(unwrap xs) b} fnil (lam z a (lam zs (fix list (all r (fun (fun r (fun (a list) r)) r))) [ fcons a [{[(unwrap y) y] a b} fnil fcons zs]]))])))))))]
```


