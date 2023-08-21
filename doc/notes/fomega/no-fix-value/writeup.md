
# Fixed Points in Plutus Core

The short version is that if we define `(fix x A M)` to be
```
[(unwrap (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))) (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))]
```
then we have:
```
(fix x A M) 
== [(unwrap (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))) (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))]
-> [(lam y (fix a (fun a A)) [[(unwrap y) y]/x]M) (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))]
-> [[(unwrap (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))) (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))]/x]M
== [(fix x A M)/x]M
```
and so defining `(fix x A M)` in this way results in two evaluation steps, where before there was only one evaluation step. Thus, any sequence of evaluation rewrites in Plutus Core with explicit term-level fixed points becomes at most twice as long when explicit term-level fixed points are removed, instead being implicitly present according to the above scheme. In practice, most sequences of rewrites involving `(fix x A M) -> [(fix x A M)/x]M` are not composed entirely of that rule, and the number of extra rewrites will be more modest. Note also that `M` occurs twice in the definition above, which may be undesirable for large `M`. If our implementation does not reduce the two copies of `M` in parallel, we may reduce `M` to normal form twice before performing the sequence of rewrites above. The resulting sequence of rewrites is still at most twice as long as the original.

## Recursion in the Untyped Lambda Calculus

The lambda calculus admits a fixed point combinator `Y` with the property that for all `g`, `Yg = g(Yg)`. While there are many terms with this property, the most popular definition is
```
Y = (lam f [(lam x [f [x x]]) (lam x [f [x x]])])
```
Observe that under a normal order (lazy) evaluation strategy we have, for every `f`:
```
Yg
== [(lam f [(lam x [f [x x]]) (lam x [f [x x]])]) f]
-> [(lam x [g [x x]]) (lam x [g [x x]])]
-> [g [(lam x [g [x x]]) (lam x [g [x x]])]]
== [g [(lam f [(lam x [f [x x]]) (lam x [f [x x]])]) g]]
== g(Yg)
```
as promised. However, under a strict evaluation strategy we have:
```
Yg
== [(lam f [(lam x [f [x x]]) (lam x [f [x x]])]) g]
-> [(lam f [f [(lam x [f [x x]]) (lam x [f [x x]])]]) g]
-> [(lam f [f [f [(lam x [f [x x]]) (lam x [f [x x]])]]]) g]
-> [(lam f [f [f [f [(lam x [f [x x]]) (lam x [f [x x]])]]]]) g]
-> ...
```
and so on. The top-level application is never reduced, and `g` is never substituted for the variable `f`!

One way to work around this problem is to define a different `Yg` for every term `g`, building the substitution of `g` for `f` into the definition:
```
Yg = [(lam x [g [x x]]) (lam x [g [x x]])]
```
Then under both strict and lazy evaluation strategies, we have:
```
Yg
== [(lam x [g [x x]]) (lam x [g [x x]])
-> [g [(lam x [g [x x]]) (lam x [g [x x]])]]
== g(Yg)
```

Plutus Core uses a strict evalutation strategy, and accordingly we will use this last style of fixed point in the language.

## How to Type Fixed Points

Following (Harper 2016), we show type-level fixed points allow us to type term-level fixed points. Specifically, if for each type `A :: type`, expression `M : A`, and variable `x` our language admits a type `self(A) :: type ` and expressions `self{A}(x.M)` and `unroll(M)` with typing:
```
 Γ, x : self(A) ⊢ M : A
----------------------------
 Γ ⊢ self{A}(x.M) : self(A)

 Γ ⊢ M : self(A)
--------------------
 Γ ⊢ unroll(M) : A
```
and evaluation given by:

+ `self{A}(x.M)` is a value (in normal form).

+ if `M` evaulates to `M'`, then `unroll(M)` evaluates to `unroll(M')`.

+ `unroll(self{A}(x.M))` evaluates to `[self{A}(x.M)/x]M`.

then we can define a term `(fix x A M)` with typing given by:
```
 Γ,x : A ⊢ M : A
---------------------
 Γ ⊢ (fix x A M) : A
```
with the property that `(fix x A M)` reduces to `[(fix x A M)/x]M`. (i.e., we have a term-level fixed point operator). Specifically, we define `(fix x A M)` to be `unroll(self{A}(y.[unroll(y)/x]M))`. This definition is admissible via:
```
 x : A free in M : A
--------------------------
 Γ, x : A ⊢ M : (fun A A)
---------------------------------------                          ------------------------------
 Γ, x : A, y : self(A) ⊢ M : (fun A A)                            Γ, y : self(A) ⊢ y : self(A)     
--------------------------------------------                    ---------------------------------
 Γ y : self (A) ⊢ (lam x [M x]) : (fun A A)                      Γ, y : self(A) ⊢ unroll(y) : A
-------------------------------------------------------------------------------------------------
                            Γ,x : A, y : self(A) ⊢ [(lam x A [M x]) unroll(y)] : A
                           ========================================================
                            Γ,x : A, y : self(A) ⊢ [unroll(y)/x]M : A
                           -----------------------------------------------
                            Γ,x : A ⊢ self{A}(y.[unroll(y)/x]M) : self(A)
                           ------------------------------------------------------
                            Γ,x : A ⊢ unroll(self{A}(y.[unroll(y)/x]M) : A
```
and has the requried property with respect to evaulation:
```
unroll(self{A}(y.[unroll(y)/x]M))
-> [self{A}(y.[unroll(y)/x]M)/y]([unroll(y)/x]M)
== [unroll(self{A}(y.[unroll(y)/x]M))/x]M
```

Thus, if we can find definitions of `self(A)`, `self{A}(x.M)`, and `unroll(M)` in Plutus Core such that the above typing and reduction rules are admissible, we will be able to define `(fix x A M)` in the language.

In Plutus Core, we have isorecursive types in the form of:
```
 Γ,a :: type ⊢ A :: type
----------------------------
 Γ ⊢ (fix a A) :: type


 Γ,a :: type ⊢ A :: type    Γ ⊢ M : [(fix a A)/a]A
---------------------------------------------------
          Γ ⊢ (wrap a A M) : (fix a A)


 Γ ⊢ M : (fix a A)
---------------------------------
 Γ ⊢ (unwrap M) : [(fix a A)/a]A
```
where `(unwrap (wrap a A V))` reduces to `V` for any term value `V` (eager evaluation). We define
```
self(A) == (fix a (fun a A))

self{A}(x.M) == (wrap a (fun a A) (lam x (fix a (fun a A)) M))

unroll(M) == [(unwrap M) M]
```
and we show that the typing rules are admissible:
```
 Γ, x : self(A) ⊢ M : A
==================================
 Γ, x : (fix a (fun a A)) ⊢ M : A
------------------------------------------------------------------
 Γ ⊢ (lam x (fix a (fun a A)) M) : [(fix a (fun a A))/a](fun a A)
------------------------------------------------------------------------
 Γ ⊢ (wrap a (fun a A) (lam x (fix a (fun a A)) M)) : (fix a (fun a A))
========================================================================
 Γ ⊢ self{A}(x.M) : self(A)


Γ ⊢ M : self(A)
==========================                    
Γ ⊢ M : (fix a (fun a A))                      Γ ⊢ M : self(A)
------------------------------------------    ===========================
Γ ⊢ (unwrap M) : (fun (fix a (fun a A)) A)     Γ ⊢ M : (fix a (fun a A)) 
-----------------------------------------------------------------------
                             Γ ⊢ [(unwrap M) M] : A
			    ========================
			      Γ ⊢ unroll(M) : A
```
We must also show that the reduction rules are admissible. First, we observe that
```
self{A}(x.M) == (wrap a (fun a A) (lam x (fix a (fun a A)) M)) 
```
is a value (is in weak head normal form). Next, supposing `M` evaluates to `M'` we have
```
unroll(M)
== [(unwrap M) M]
-> [(unwrap M') M']
== unroll(M')
```
and finally we have
```
unroll(self{A}(x.M))
== [(unwrap (wrap a (fun a A) (lam x (fix a (fun a A)) M))) (wrap a (fun a A) (lam x (fix a (fun a A)) M))]
-> [(lam x (fix a (fun a A)) M) (wrap a (fun a A) (lam x (fix a (fun a A)) M))]
-> [(wrap a (fun a A) (lam x (fix a (fun a A)) M))/x]M
== [self{A}(x.M)/x]M
```
as required.

At this point we know term-level fixed points are definable in Plutus Core. Precisely, we define
```
(fix x A M)
== unroll(self{A}(y.[unroll(y)/x]M))
== unroll(wrap (fun a A) (lam y (fix a (fun a A)) [unroll(y)/x]M))
== [(unwrap (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))) (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))]
```
and observe that, as expected:
```
(fix x A M) 
== [(unwrap (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))) (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))]
-> [(lam y (fix a (fun a A)) [[(unwrap y) y]/x]M) (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))]
-> [[(unwrap (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))) (wrap (fun a A) (lam y (fix a (fun a A)) [[(unwrap y) y]/x]M))]/x]M
== [(fix x A M)/x]M
```

Notice that if we erase the type information (including `wrap` and `unwrap`) from the above term we obtain
```
[(lam y ([[y y]/x]M) ) (lam y ([[y y]/x]M))]
== [(lam y [(lam x M) [y y]]) (lam y [(lam x M) [y y]])]
```
recovering the something familiar in the untyped setting.


