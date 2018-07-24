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

Following (Harper 2016), we may use the machinery of recursive types to define recursive terms, even if our language has no explicit term-level recursion. In Plutus Core, we have isorecursive types in the form of:
```
Γ,a :: (type) ⊢ A :: (type)
----------------------------
  Γ ⊢ (fix a A) :: (type)


Γ,a :: (type) ⊢ A :: (type)    Γ ⊢ M : [(fix a A)/a]A
------------------------------------------------------
              Γ ⊢ (wrap a A M) : (fix a A)


      Γ ⊢ M : (fix a A)
--------------------------------
Γ ⊢ (unwrap M) : [(fix a A)/a]A
```

