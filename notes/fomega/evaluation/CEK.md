# Two versions of the CEK machine

Version 1 has values in the environment. Version 2 has closures (pairs
of values and environments) in the environment.

In my limited testing I have found version 1 to be faster and I think
it is simpler.

The main point of this document is so that we can discuss whether to
use version 1 in the implementation. Version 2 is described as a
comparison.

I have formalised both of these version in Agda and they can used via
`plc-agda`.

The relevant files are:

[Version 1](../../../metatheory/Algorithmic/CEKV.lagda.md)

[Version 2](../../../metatheory/Algorithmic/CEKC.lagda.md)

## 1. Value version

Note: that this makes no attempt to delay doing type
substitutions. This would be a further optimisation and I think it
could be modified to do so. To get an idea, and avoid this issue, I
guess one can focus on the other parts of the syntax (constants,
lambda, application, wrap/unwrap).

Values and environments are mutually defined. Environments only appear
under binders, they have entries for all free variables in the term
but no entry for the variable (`α` or `x`) bound by the binder.

```
V := con cn
   | abs ɑ (M , ⍴)
   | lam x (M , ρ)
   | iwrap A B V
ρ := []
   | ρ[x |-> V]
```

Frames: note that we never have pairs of values and environments, only
pairs of terms and environments in frames. In the builtin case, we
stash the environment `ρ` that we were in when we began processing the
builtin. We use ρ to evaluate each of the builtin arguments in,
kicking off evaluation of each argument with the original ρ. The
builtin frame refers to the point where we are processing the
arguments from left to right, the already evaluated args are stored in
`Vs` and the as yet unevaluated args are stored in `Ms`.

```
f := [_ (M,ρ) ]
   | [V _]
   | {_ A}
   | wrap A B _
   | unwrap _
   | builtin b As Vs _ Ms ρ
```

Stacks of frames
```
s := .
   | s , f
```

States: note that only the term computing (`|>`) phase has an
environment. In the value phase (`<|`) the environment can be thought
of as being inside the value.
```
σ := s ; ρ |> M -- term in focus
   | s <| V     -- value in focus
   | <> A       -- error
   | [] V       -- done
```

The machine. Term configuration:
```
s ; ρ |> x                      |-> s <| ρ[ x ]
s ; ρ |> lam x L                |-> s <| lam x (L , ρ)
s ; ρ |> [L M]                  |-> s , [_ (M,ρ)]  ; ρ |> L
s ; ρ |> abs α L                |-> s <| abs α (L , ρ)
s ; ρ |> {L A}                  |-> s , {_ A} ; ρ |> L
s ; ρ |> wrap A B L             |-> s , wrap A B _ ; ρ |> L
s ; ρ |> unwrap L               |-> s , unwrap _ ; ρ |> L
s ; ρ |> con c                  |-> s <| con c
s ; ρ |> builtin b As           |->
 | bn computes on As to V       = s <| V
 | bn computes on As to error A = <> A
s ; ρ |> builtin b As (M :: Ms) |-> s , builtin b As [] _ Ms ρ ; ρ |> M
s ; ρ |> error A                |-> <> A
```
Value configuration:
```
.                                <| V           |-> [] V
s , [_ (M,ρ)]                    <| V           |-> s , [V _] ; ρ |> M
s , [(lam x (M,ρ)) _]            <| V           |-> s ; ρ [ x |-> V ] |> M
s , {_ A}                        <| abs α (M,ρ) |-> s ; ρ |> M [ α / A ]*
s , wrap A B _                   <| V           |-> s <| wrap A B V
s , unwrap _                     <| wrap A B V  |-> s <| V
s , builtin b As Vs _ [] ρ       <| V           |->
 | bn computes on As (Vs ++ [V]) to V'      = s <| V'
 | bn computes on As (VS ++ [V]) to error A = <> A
s , builtin b As Vs _ (M ∷ Ms) ρ <| V           |->
  s , builtin b As (Vs ++ [V]) _ Ms ρ ; ρ |> M
```

One can discharge a value back to a term. Note that this cannot change
the head symbol of a value though, so a lambda value is never going to
turn into a constructor etc. If we only want to check if the answer is
true/false then it's not necessary to discharge, we can just look at
the value.

This version is, I think, the same as the version of CEK described in
the 1986 Tech Report "Control Operators, the SECD-machine, and the
λ-calculus" by Felleisen and Friedman, page 5, table 1,
https://legacy.cs.indiana.edu/ftp/techreports/TR197.pdf. Their machine
looks a bit different as they have 3-tuples of a term or nothing, an
environment and a continuation for the state. Our `s ; ρ |> M` is
written `(M , ρ , s)` and our `s <| V` is written `(%, 0, s ret V)`
where % signifies there is no term in focus and 0 is the empty
environment.

## 2. Closure version

This is the version described in the spec and also the version used in
the implementation. I have also formalised this.

Values are simpler with just terms under binders:
```
V := con cn | abs ɑ M | lam x M | iwrap A B V
```
Closures:
```
C := (V , ρ)
```
Environments contain closures:
```
ρ := [] | ρ[x |-> C]
```
Frames: note the contain closures instead of just values
```
f := [_ (M,ρ)]
   | [C _]
   | {_ A}
   | wrap A B _
   | unwrap _
   | builtin b As Cs _ Ms ρ
```

Stacks of frames
```
s := .
   | s , f
```

States contain environments in both the term and value configuration.
```
σ := s ; ρ |> M
   | s ; ρ <| V
   | <> A
   | [] C
```

The machine. Term configuration:
```
s ; ρ |> x                      |-> s ; ρ' <| V where (V , ρ' ) = ρ[ x ]
s ; ρ |> lam x L                |-> s ; ρ <| lam x L
s ; ρ |> [L M]                  |-> s , [_ (M,ρ)]  ; ρ |> L
s ; ρ |> abs α L                |-> s ; ρ <| abs α L
s ; ρ |> {L A}                  |-> s , {_ A} ; ρ |> L
s ; ρ |> wrap A B L             |-> s , wrap A B _ ; ρ |> L
s ; ρ |> unwrap L               |-> s , unwrap _ ; ρ |> L
s ; ρ |> con c                  |-> s ; ρ <| con c
s ; ρ |> builtin b As           |-> s ; ρ' |> M
  where bn computes on As to (M,ρ')
s ; ρ |> builtin b As (M :: Ms) |-> s , builtin b As [] _ Ms ρ ; ρ |> M
s ; ρ |> error A                |-> <> A
```
Value configuration:
```
.                                 ; ρ <| V          |-> [] (V,ρ)
s , [_ (M,ρ)]                     ; ρ <| V          |-> s , [(V,ρ) _] ; ρ' |> M
s , [(lam x (M,ρ')) _]            ; ρ <| V          |-> s ; ρ [ x |-> (V,ρ) ] |> M
s , {_ A}                         ; ρ <| abs α M    |-> s ; ρ |> M [ α / A ]*
s , wrap A B _                    ; ρ <| V          |-> s ; ρ <| wrap A B V
s , unwrap _                      ; ρ <| wrap A B V |-> s ; ρ <| V
s , builtin b As Cs _ [] ρ'       ; ρ <| V          |-> s ; ρ'' |> M
 where bn computes on As (Cs ++ [(V,ρ)]) to (M,ρ'')
s , builtin b As Cs _ (M ∷ Ms) ρ' ; ρ <| V         |->
  s , builtin b As (Cs ++ [(V,ρ)]) _ Ms ρ' ; ρ' |> M
```

There is a bit of a descrepency in the
spec/implementation/formalisation when it comes to which environment
builtin arguments should be evaluated in and also what is returned
from when a builtin computes. The formalisation evaluates each
argument in the same initial environment and returns a closure when
the builtin computes. The spec returns a term instead of a closure and
puts the resultant term in the original environment which I believe is
unsafe. Roman spotted this problem in the implementation, so it
accumulates an environment as it processes the arguments one at a time
and then returns a closure containing the final environment which I
think is safe but gives an overapproximation of the environment
required as it may contain bindings from a builtin arg that is not
relevant, e.g., if we have a builtin for if-then-else, then
environment bindings for both branches would be returned even though
we only pick one branch.