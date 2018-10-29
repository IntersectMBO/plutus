# Plutus IR design proposal

## Syntax

We are not going to have a concrete syntax initially, but since the syntax of Plutus Core already
corresponds closely to the AST structure giving an illustrative syntax is the easiest way to describe
the proposed AST.

The syntax is a strict superset of Plutus Core, and this syntax should be read as an extension to the Plutus
Core grammar, and references productions from it. Where we modify the syntax of Plutus Core we will
list only the additions, marking them explicitly with `+`.

We also require syntax with lists of subparts. We denote a list of `t`-productions with `t..`.

```
VarDecl VD      := (vardecl x T)
TyVarDecl TVD   := (tyvardecl alpha K)

Term L, M, N    := + (let R B.. M)

Recursivity R   := (nonrec)
                   (rec)
Binding B       := (termbind VD L)
                   (typebind TVD T)
                   (datatypebind D)

Datatype D      := (datatype
                      TVD   # the type variable for the datatype
                      TVD.. # the argument type variables of the datatype
                      x     # the name of the destructor function
                      VD..  # the constructors of the datatype
                   )
```

Here is an example, constructing `[1]`:
```
# bind List
(let (rec)
    (datatypebind
        (datatype
            (tyvardecl List (fun (type) (type)))
            (tyvardecl a (type))
            match_List
            (vardecl
                Nil
                [List a]
            )
            (vardecl
                Cons
                (fun a [List a])
            )
        )
    )
    # bind int64 for convenience
    (typebind (tyvardecl int (type)) [(con integer) (con 64)])
    # apply cons to 1 and nil
    [ { Cons int } (con 64 ! 1) { Nil int } ]
)
```

Another, implementing `fromMaybe`:
```
# bind Maybe
(let (nonrec)
    (datatypebind
        (datatype
            (tyvardecl Maybe (fun (type) (type)))
            (tyvardecl a (type))
            match_Maybe
            (vardecl
                Nothing
                [Maybe a]
            )
            (vardecl
                Just
                (fun a [Maybe a])
            )
        )
    )
    (abs a (type)
        (lam default a
            (lam arg [Maybe a]
                # match on the arg, producing an a, giving the default
                # in the Nothing case and using the identity function
                # in the Just case
                [ { match_Maybe a } arg default (lam x a x) ]
            )
        )
    )
)
```

## Semantics

Plutus IR is defined by its compilation into Plutus Core. This process will eventually be formalized,
but for now we give a schematic description.

### Let bindings

#### Non recursive

Non-recursive term let bindings are translated as lambdas in the usual way, and non-reursive type bindings are
translated as type abstractions.

#### Recursive

There is no way to have mutual recursion between terms and types, so if both terms and types are defined
in a let binding, we separate the two groups out and handle them separately.

Recursive term bindings are compiled using the n-ary fixpoint combinator. They must therefore all be of
function type. It is the responsibility of the author to transform bindings which are not of this type
beforehand (e.g. by thunking it and forcing at the recursion sites.)

Singly self-recursive type bindings are compiled with a type variable of the appropriate kind in scope.
We then take the fixpoint over that type variable.

Mutually recursive type bindings are not currently supported.

### Datatypes

Datatypes are compiled into:

- A datatype.
    - This is the usual Scott-encoded type.
- Constructor functions for each constructor.
    - These have the types specified in the datatype declaration.
- A destructor function.
    - This has the type `forall tvs . [datatype tvs] -> <Scott-encoded type>`. Once applied,
      one can use the Scott-encoded type as a matcher as usual.

These are then let-bound as usual.

We must take some care over this process, which is described in detail in the GHC Core to Plutus Core
compiler, and which I will not repeat now (but should eventually move to the specification).

## Validity

### Mutually recursive types

The syntax of Plutus IR suggests that you can write mutually recursive datatypes, even though
we don't know how to compile those yet. I think we will eventually be able to cover all
types defined with this syntax, but until then, validity of Plutus IR programs will be somewhat
determined simply by *whatever we are able to compile*.

### Typechecking

Similarly, while we will define a typing judgement for Plutus IR, we will probably not
write a typechecker for it initially, and rather will compile it to Plutus Core before typechecking.

A typechecker is desirable in the long run to help catch bugs and give better error messages.

### Value restriction

Since type-lets are going to be desugared as type abstractions, a type-let whose body is not
a value will fail the Plutus Core value restriction, and there is no attempt to prevent this
in the Plutus IR syntax. It will simply compile into an invalid Plutus Core program.

## Typing

Typing rules are largely the same as Plutus Core.

(I should write out some real rules for this, but everything being variadic makes it a bit noisy.)

Let bindings are straightforward: they introduce names into the context with their declared
type or kind. For recursive let bindings we typecheck each binding under the assumption that
all the bindings have their declared type or kind.

We do need to state something more complex about datatype bindings: they introduce a
number of names with various types or kinds, with the correctness conditions being:
- The type variable declarations are well-kinded.
- The application of the datatype to its type variables is well-kinded and of kind `(type)`.
- The constructor argument types are all well-kinded and of type `(type)`.

## Design notes

### Why do we need variadic syntax?

`letrec` is inherently about binding an arbitrary number of mutually recursive bindings, so
we need to be able to write that.

### Why is `let` variadic?

`letrec` obviously needs to be variadic, since the whole point is to have multiple bindings
that reference each other.

`let` doesn't *need* to be variadic, but it's symmetrical, convenient, and no harder to support.

### Why is there a special datatype binding?

Datatype bindings are weird in that they bind multiple names, which are part of the binding
(the type, the constructors, the destructor). So we can't handle it as a normal "type binding" since
it also declares other things.

### Why are variable declarations reified in the syntax?

It's very helpful to have a syntax form for variable declarations, since the syntax is too
homogeneous when everything is just names. For example, in the datatype declaration we have
a whole series of type variable declarations. I think we could just about parse the version
with them all flattened, but it's much clearer when they're reified.

I think this is quite useful and arguably worth introducing in the Plutus Core syntax too.

### Why does `datatype` bind its type variables?

The current syntax is very close to the GADT-style datatype declaration common in Haskell
and other languages. Having the type variable bound outside the constructor type is helpful
because we will in practice want to instantiated it in a variety of ways, e.g. for `Just`:

```
# the constructor declaration
(constr Just (fun a [Maybe a]))
# the type of the constructor functoin
forall a . a -> Maybe a
# the datatype itself
\a :: * -> forall r . r -> (a -> r) -> r
# the type of the matcher function
forall a r . Maybe a -> r -> (a -> r) -> r
```

So we need to deconstruct the declaration to throw away the output type and replace it, at least.
But this is doable.

## Discussion points

### I hate your keyword suggestions

Better suggestions welcome! This also is not intended to fix a concrete syntax.

### Should we have `match`?

Currently there is no `match` syntax, instead we expose destructor functions.

This has the following advantages:
- Easier to translate into Plutus Core
- Only allowing "simple" matches, which are all we're going to support anyway.

It does have some disadvantages:
- Need an additional name for the destructor.
- The destructor needs to be instantiated at the result type of the match, whereas for a match
  syntax this could be inferred.

I think these are fine for an IR.

### Can we simplify the datatype-binding syntax?

Currently it's a bit clumsy.
