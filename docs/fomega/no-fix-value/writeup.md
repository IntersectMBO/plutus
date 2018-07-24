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
and so defining `(fix x A M)` in this way results in two evaluation steps, where before there was only one evaluation step.

Note also that `M` occurs twice in this definition of `(fix x A M)`.