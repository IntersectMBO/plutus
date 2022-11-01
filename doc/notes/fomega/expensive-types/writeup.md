# Deciding Equality of Types Can Be Very Expensive

Whether implicitly or explicitly, we must beta-reduce types of Plutus Core to normal form during typechecking. Here we construct a family of Plutus Core types that take a very long time to reduce to normal form. The existence of such types is something that must be accounted for in the design of the larger system.


Since we are using system F-omega, every term of the simply-typed lambda calculus defines a type of Plutus Core, and beta-reducing that type is the same as beta-reducing the original term. This allows us to apply results concerning beta-reduction in the simply-typed lambda calculus to our setting.

In particular, following [(Schwichtenberg 1982)](https://github.com/Cubesoup/literature-review-notes/blob/master/papers/schwichtenberg-1982-complexity-of-normalization-in-the-pure-typed-lambda-calculus.pdf), we define a series of kinds indexed by the natural numbers:
```
0   = *
N+1 = N -> N
```
So, for example:
```
1 = * -> *
2 = 1 -> 1 = (* -> *) -> (* -> *)
3 = 2 -> 2 = (1 -> 1) -> (1 -> 1) = ((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *))
...
```
and so on. Next, we define a familty of types, also indexed by the natural numbers:
```
t_1 := (\(f::1).\(x::0). f(f x)) 
t_N := (\(f::N).\(x::(N-1)). f(f x)) t_(N-1)
```
So, for example:
```
t_2 := (\(f::2).\(x::1). f(f x)) (\(f::1).\(x::0). f(f x))
t_3 := (\(f::3).\(x::2). f(f x)) (\(f::2).\(x::1). f(f x)) (\(f::1).\(x::0). f(f x))
...
```
and so on. Scwichtenberg shows that the number of steps `s_N` involved in any reduction sequence of `t_N` to normal form is such that `s_N >= F2(N-2) - N`, where `F2` is defined by:
```
F2(0) = 1
F2(N+1) = 2^(F2(N))
```
So for example `F2(3)` is `16` and `F2(4)` is `2^(2^(2^(2^1))) = 65536`.

This gives types like `t_7`, which fully written out looks like:
```
(\(f::(((((((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *))) -
> (((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *)))) -> ((((*
-> *) -> (* -> *)) -> ((* -> *) -> (* -> *))) -> (((* -> *) ->
(* -> *)) -> ((* -> *) -> (* -> *))))) -> (((((* -> *) -> (* -
> *)) -> ((* -> *) -> (* -> *))) -> (((* -> *) -> (* -> *)) ->
((* -> *) -> (* -> *)))) -> ((((* -> *) -> (* -> *)) -> ((* ->
*) -> (* -> *))) -> (((* -> *) -> (* -> *)) -> ((* -> *) -> (*
-> *)))))) -> ((((((* -> *) -> (* -> *)) -> ((* -> *) -> (* ->
*))) -> (((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *)))) ->
((((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *))) -> (((* ->
*) -> (* -> *)) -> ((* -> *) -> (* -> *))))) -> (((((* -> *) -
> (* -> *)) -> ((* -> *) -> (* -> *))) -> (((* -> *) -> (* ->
*)) -> ((* -> *) -> (* -> *)))) -> ((((* -> *) -> (* -> *)) ->
((* -> *) -> (* -> *))) -> (((* -> *) -> (* -> *)) -> ((* -> *
) -> (* -> *)))))))).\(x::((((((* -> *) -> (* -> *)) -> ((* ->
*) -> (* -> *))) -> (((* -> *) -> (* -> *)) -> ((* -> *) -> (*
-> *)))) -> ((((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *))
) -> (((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *))))) -> (
((((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *))) -> (((* ->
*) -> (* -> *)) -> ((* -> *) -> (* -> *)))) -> ((((* -> *) ->
(* -> *)) -> ((* -> *) -> (* -> *))) -> (((* -> *) -> (* -> *)
) -> ((* -> *) -> (* -> *))))))). f(f x)) (\(f::((((((* -> *)
-> (* -> *)) -> ((* -> *) -> (* -> *))) -> (((* -> *) -> (* ->
*)) -> ((* -> *) -> (* -> *)))) -> ((((* -> *) -> (* -> *)) ->
((* -> *) -> (* -> *))) -> (((* -> *) -> (* -> *)) -> ((* -> *
) -> (* -> *))))) -> (((((* -> *) -> (* -> *)) -> ((* -> *) ->
(* -> *))) -> (((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *)
))) -> ((((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *))) ->
(((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *))))))).\(x::((
(((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *))) -> (((* ->
*) -> (* -> *)) -> ((* -> *) -> (* -> *)))) -> ((((* -> *) ->
(* -> *)) -> ((* -> *) -> (* -> *))) -> (((* -> *) -> (* -> *)
) -> ((* -> *) -> (* -> *)))))). f(f x)) (\(f::(((((* -> *) ->
(* -> *)) -> ((* -> *) -> (* -> *))) -> (((* -> *) -> (* -> *)
) -> ((* -> *) -> (* -> *)))) -> ((((* -> *) -> (* -> *)) -> (
(* -> *) -> (* -> *))) -> (((* -> *) -> (* -> *)) -> ((* -> *)
-> (* -> *)))))).\(x::((((* -> *) -> (* -> *)) -> ((* -> *) ->
(* -> *))) -> (((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *)
)))). f(f x)) (\(f::((((* -> *) -> (* -> *)) -> ((* -> *) -> (
* -> *))) -> (((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *))
))).\(x::(((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *)))).
f(f x)) (\(f::(((* -> *) -> (* -> *)) -> ((* -> *) -> (* -> *)
))).\(x::((* -> *) -> (* -> *))). f (f x)) (\(f::((* -> *) ->
(* -> *))).\(x::(* -> *)). f (f x)) (\(f::(* -> *)).\(x::*). f
(f x))
```
While the term is rather large, it is not prohibitively so, and Schwichtenberg's result tells us that reducing it to normal form must take at least `F2(5) - 7 = (2^65536) - 7` steps.

Note also that most of the size of the term comes from the kind signatures associated with type-level lambdas. In a system with "Curry-style kinding", `t_7` is much smaller. It is also easy to see that the size of `t_N` grows far, far more slowly than `F2(N-2) - N`.


