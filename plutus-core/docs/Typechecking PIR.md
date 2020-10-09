## Intro

Let's say we have this imaginary Plutus Tx program:

```
data Success = MkSuccess
MkSuccess
```

I'm calling it "imaginary", because we probably can't write it as is and we probably first introduce the data definition, type check it, add it to the Haskell metacontext and only then type check `MkSuccess` in the extended metacontext. But even if we can't express this Plutus Tx program directly, we do this indirectly as we produce the following Plutus IR program as an intermediate result of compilation of the "implicit" program above:

```
let data Success :: * = MkSuccess in
  MkSuccess
```

And that PIR program is now suddenly ill-scoped, even though it's very similar to the original program that was not considered to be ill-scoped.

Moreover, we know that the produced Plutus IR program will compile to a perfectly legal Plutus Core program. I.e. we have:

- a well-typed Plutus Tx program
- that becomes an ill-scoped Plutus IR program being compiled
- that becomes a well-typed Plutus Core program being further compiled 

It would be nice if we found a way of type checking PIR in a way that supports programs like that.
So we have two problems:

1. type checking problem: how do we type check PIR in a way that doesn't rule out valid programs like that one?
2. evaluation problem (Michael's point): but is that even a valid program? If we had an evaluator for Plutus IR, what would it evaluate to?

I'll start with the evaluation problem.

## The evaluation problem

Indeed, what would we evaluate such a program to? This question was bugging me until I realized that we don't really have any evaluators. The CK machine is not an evaluator -- it's a normalizer. The CEK machine is not an evaluator either -- it's a crappy normalizer ("crappy", because we don't handle types correctly, but once we define the CEK machine over Untyped Plutus Core, it'll become a proper normalizer). We even discharge the final environment into the resulting **term** (technically, a value, but a value is a term) before returning from the CEK machine. It's a normalizer, not an evaluator.

Being compiled to Plutus Core, what will the program normalize to? To a term containing a type abstraction, a lambda abstraction and a variable.

So, what would we normalize the Plutus IR program to? Itself. Because the result of the program is a constructor referencing a local data type, so we have to keep the data binding and so we get the original program back. I.e. just like the fully compiled PLC program doesn't evaluate to a constant, the intermediate PIR program doesn't evaluate to a constant either.

I.e. there does seem to exist a sensible "evaluation" semantics for such PIR programs.

## The type checking problem

What is the type of the original imaginary Plutus Tx program? Well, it doesn't have any type. The type of `True` is `Bool` once the latter is added to the metacontext, but the whole program doesn't really have any type. For Plutus Tx we're only interested in type checking things inside a program.

Why can't we use the same strategy for Plutus IR? Type check things inside a program, but don't attempt to find the type of the whole program, because it doesn't have one in the general case.

Here's how an implementation of this idea would look like.

Like before, we have two type checking modes: `infer` and `check`. Unlike before, `check` now receives a `Maybe Type` (as opposed to `Type`) when it comes to type checking

- `inferType term`  -- infer the type of `term`
- `checkType (Just ty) term`  -- type check `term` against `ty`
- `checkType Nothing term`  -- type check `term` and ignore its type

Kind checking remains the same:

- `inferKind ty`  -- infer the kind of `ty`
- `checkKind k ty`  -- kind check `ty` against `k`

The idea is that we type check a Plutus IR program against `Nothing`, i.e. we're only interested in ensuring that all things are well-typed within their scopes, but we're not interested in returning any resulting type or type checking against any type. This way we handle the top-level scope in a different way than any inner scope, which allows us to

1. accept a valid program whose result references some of the top-level data bindings
2. reject a program with a type escaping its scope

### The type checking algorithm

Once we reach a single possibly recursive data-binding let (the algorithm should directly generalize to mutually recursive bindings, we only show a non-mutual example for readability)

```
let D :: K = D_body in e
```

we:

1. kind check `D_body` in the current context extended with `D :: K` (because of recursion `D_body` may contain references to `D`) against `K`. I.e. call `checkKind K D`
2. type check `e` in the current context extended with `D :: K` and `c_i : A_i` for each constructor of `D` **in the same mode that the whole `let` is being type checked in**. I.e. if the whole let is type checked against `Nothing`, then `e` is type checked against `Nothing` as well and similarly for `Just ty` for some `ty`

Type checking term-binding let is similar:

```
let v : A = x in e
```

1. kind check `A` against `*` in the current context
2. type check `x` against `Just A` in the current context extended with `v : A` (due to the possible recursion)
3. type check `e` in the current context extended with `v : A` **in the same mode that the whole `let` is being type checked in**. I.e. if the whole let is type checked against `Nothing`, then `e` is type checked against `Nothing` as well and similarly for `Just ty` for some `ty`

### Examples

Consider three different cases:

1. a program consisting of a single `data-let`:

```
let data Success :: * = MkSuccess in
  MkSuccess
```

We type check it against `Nothing`, hence the final `MkSuccess` is type checked against `Nothing`, hence it's fine that its type is `Success`, because after ensuring that `MkSuccess` is well-typed, we throw its type away and conclude that the program is well-typed

2. a `term-let` inside the body of a `data-let`:
```
let data Success :: * = MkSuccess in
  let x : Integer = body_of_unrelated_x in
    in MkSuccess
```

As before, the program is being type checked against `Nothing`, and since the body of a let type checks in the same mode as the whole term the inner `let` also type check against `Nothing`, hence it's again fine to return `MkSuccess`

3. a `data-let` inside the binding of a `term-let`:

```
let x : Integer =
  let data Success :: * = MkSuccess in
    MkSuccess
in x
```

As before, the program type checks against `Nothing`. Once we reach `MkSuccess` in the body of the inner `let`, we try to type check it against `Integer` (the expected type of the binding), because we always type check a binding  against a particular type due to

> 2. type check `x` against `Just A` in the current context extended with `v : A` (due to the possible recursion)

and so the type checker fails here, because the type of `MkSuccess` is `Success` rather than `Integer`.

We could have annotated `x` with any other type, the program wouldn't type check anyway. This is because the type of `x` is kind checked in the empty context due to

> 1. kind check `A` against `*` in the current context

and `Success` is out of scope in the empty context.

### Typing rules

Just to have everything important in a single place, we'll provide the typing rules discussed above here.

The typing rules for a possibly recursive single-term-binding `let` and a possibly recursive single-data-binding `let` should look something like:

```
[check| G !- A :: Just *]    [check| G , (v : A) !- x : Just A]    [check| G , (v : A) !- e : target]
-----------------------------------------------------------------------------------------------------
                         [check| G !- (let v : A = x in e) : target]

[check| G , (D :: K) !- D_body :: Just K]    [check| G , (D :: K) , (c_i : A_i) !- e : target]
----------------------------------------------------------------------------------------------
                 [check| G !- (let D :: K = D_body in e) : target]
```

This uses the notation described [here](https://github.com/input-output-hk/plutus/blob/bea0b9abd9554c792b6d0f667c5b4711c790b44c/language-plutus-core/src/Language/PlutusCore/TypeCheck/Internal.hs#L54-L71). Except we now use `[check| G !- x : Just A]` instead of `[check| G !- x : A]`, because we now also allow `[check| G !- x : Nothing]`.

So `[check| G !- x : target]` denotes `checkType target x` where `target :: Maybe Type`.

Note that `[check| ... ]` is overloaded and unambiguously means either `checkType` or `checkKind` depending on the context. Same for `infer`.

Finally, we amend the `infer-check` rule to account for `Nothing`:

```
[infer| G !- term : A]    case target of
                              Nothing -> ()
                              Just B  -> A ~ B
----------------------------------------------
[check| G !- term : target]
```

where `()` is a unit judgement and `~` denotes an equality check. I.e. if `target` is `Just B`, then we check that the actual type (`A`) matches the expected one (`B`), like it was before. But if `target` is `Nothing`, then we accept whatever type is inferred and ignore it.

### Conclusions

This should give us an algorithm for type checking PIR that

- doesn't rule out well-typed programs where the resulting term references some of the top-level data bindings
- rejects programs where a type escapes its scope
