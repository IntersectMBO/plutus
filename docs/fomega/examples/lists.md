The `list` type may be expressed in Plutus Core as:
```
(lam a (type) (fix list (all r (type) (fun (fun r (fun a (fun list r)) r)))))
```
with `nil` given by:
```
(abs a (type) (wrap x (all r (type) (fun r (fun (fun a (fun x r)) r)))
  (abs r (type) (lam nil r (lam cons (fun a (fun (fix x (all r (type) (fun r (fun (fun a (fun x r)) r)))) r)) nil)))))
```
and `cons` given by:
```
(abs a (type) (lam x a (lam xs (fix x (all r (type) (fun r (fun (fun a (fun x r)) r))))
  (wrap x (all r (type) (fun r (fun (fun a (fun x r)) r)))
  (abs r (type) (lam nil r (lam cons (fun a (fun (fix x (all r (type) (fun r (fun (fun a (fun x r)) r)))) r))
    [cons x xs])))))))
```


We can define `head`:
```
(abs a (type) (lam xs (fix x (all r (type) (fun r (fun (fun a (fun x r)) r))))
  [ { (unwrap xs) a }
    (error a)
    (lam h a (lam t (fix x (all r (type) (fun r (fun (fun a (fun x r)) r)))) h))]))
```
and `tail`:
```
(abs a (type) (lam xs (fix x (all r (type) (fun r (fun (fun a (fun x r)) r))))
  [ { (unwrap xs) (fix x (all r (type) (fun r (fun (fun a (fun x r)) r)))) }
    (error (fix x (all r (type) (fun r (fun (fun a (fun x r)) r)))))
    (lam h a (lam t (fix x (all r (type) (fun r (fun (fun a (fun x r)) r)))) t)) ]))
```
without too much trouble.

`fold` is tricky, but making use of the existing notes we eventually arrive at:
```
[ (unwrap (wrap t (fun t (all a (type) (all b (type) (fun b (fun (fun a (fun b b)) (fun (fix x (all r (type) (fun r (fun (fun a (fun x r)) r)))) b))))))
        (lam y (fix t (fun t (all a (type) (all b (type) (fun b (fun (fun a (fun b b)) (fun (fix x (all r (type) (fun r (fun (fun a (fun x r)) r)))) b)))))))
	(abs a (type) (abs b (type)
	(lam nilf b (lam consf (fun a (fun b b))
	(lam xs (fix x (all r (type) (fun r (fun (fun a (fun x r)) r))))
	  [ { (unwrap xs) b }
	    nilf
	    (lam z a (lam zs (fix x (all r (type) (fun r (fun (fun a (fun x r)) r))))
	      [ consf a [ { [ (unwrap y) y ] a b } nilf consf zs ]]))]))))))))
	      
  (wrap t (fun t (all a (type) (all b (type) (fun b (fun (fun a (fun b b)) (fun (fix x (all r (type) (fun r (fun (fun a (fun x r)) r)))) b))))))
        (lam y (fix t (fun t (all a (type) (all b (type) (fun b (fun (fun a (fun b b)) (fun (fix x (all r (type) (fun r (fun (fun a (fun x r)) r)))) b)))))))
	(abs a (type) (abs b (type)
	(lam nilf b (lam consf (fun a (fun b b))
	(lam xs (fix x (all r (type) (fun r (fun (fun a (fun x r)) r))))
	  [ { (unwrap xs) b }
	    nilf
	    (lam z a (lam zs (fix x (all r (type) (fun r (fun (fun a (fun x r)) r))))
	      [ consf a [ { [ (unwrap y) y ] a b } nilf consf zs ]]))])))))))
]
```


