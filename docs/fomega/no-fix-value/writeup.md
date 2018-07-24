# Recursive Types Induce Recursive Terms

The short version is that if we define `(fix x A M)` to be
```
[(unwrap (wrap a (a -> A) (\y. [((unwrap y) y)/x]M))) (wrap a (a -> A) (\y. [((unwrap y) y)/x]M))]
```
then we have:
```
(fix x A M)
== [(unwrap (wrap a (a -> A) (\y. [((unwrap y) y)/x]M))) (wrap a (a -> A) (\y. [((unwrap y) y)/x]M))]
-> (\y. [((unwrap y) y)/x]M) (wrap a (a -> A) (\y. [((unwrap y) y)/x]M))]
-> [((unwrap (wrap a (a -> A) (\y. [((unwrap y) y)/x]M))]) (wrap a (a -> A) (\y. [((unwrap y) y)/x]M))])/x]M
== [(fix x A M)/x]M
```
and so defining `(fix x A M)` in this way results in two evaluation steps, where before there was only one evaluation step. Thus, any sequence of evaluation rewrites in Plutus Core with explicit term-level fixed points becomes at most twice as long when explicit term-level fixed points are removed, instead being implicitly present according to the above scheme. In practice, most sequences of rewrites involving `(fix x A M) -> [(fix x A M)/x]M` are not composed entirely of that rule, and the number of extra rewrites will be more modest. Note also that `M` occurs twice in the definition above, which may be undesirable for large `M`.

## In Depth

Following (Harper 2016), we may use the machinery of recursive types to define recursive terms, even if our language has no explicit term-level recursion. Specifically, if for each type `A`, expression `M`, and variable `x` our language admits a type `self(A)` and expressions `self{A}(x.M)` and `unroll(e)` with typing:
```
  Γ, x : self(A) ⊢ M : A
---------------------------
Γ ⊢ self{A}(x.M) : self(A)

 Γ ⊢ M : self(A)
------------------
Γ ⊢ unroll(M) : A
```
and evaluation given by:

+ `self{A}(x.M)` is a value (in normal form).

+ if `M` evaulates to `M'` in one step, then `unroll(M)` evaluates to `unroll(M')` in one step.

+ `unroll(self{A}(x.M))` evaluates to `[self{A}(x.M)/x]M` in one step.

then we can define a term `(fix x A M)` with typing given by:
```
  Γ,x : A ⊢ M : A
--------------------
Γ ⊢ (fix x A M) : A
```
with the property that `(fix x A M)` reduces to `[(fix x A M)/x]M`. (i.e., we have a term-level fixed point operator). Specifically, one must define `(fix x A M)` to be `unroll(self{A}(y.[unroll(y)/x]M))`, and indeed
```
unroll(self{A}(y.[unroll(y)/x]M))
-> [self{A}(y.[unroll(y)/x]M)]
```


In Plutus Core, we have isorecursive types in the form of:
```
Γ,a :: K ⊢ A :: K
----------------------------
  Γ ⊢ (fix a A) :: K


Γ,a :: K ⊢ A :: K    Γ ⊢ M : [(fix a A)/a]A
------------------------------------------------------
              Γ ⊢ (wrap a A M) : (fix a A)


      Γ ⊢ M : (fix a A)
--------------------------------
Γ ⊢ (unwrap M) : [(fix a A)/a]A
```
where `(unwrap (wrap a A V)` reduces to `V` for any term value `V` (eager evaluation).

