# Isorecursive types for system F-omega

Following (Dreyer 2005 -- PhD Thesis), I propose the following rules for `wrap` and `unwrap` in Plutus Core:

```
Γ ⊢ Q :: (type)    Q = E{(fix a C)}     Γ ⊢ M : E{[(fix a C)/a]C}
------------------------------------------------------------------
Γ ⊢ (wrap a C M) : Q

Γ ⊢ Q :: (type)    Q = E {(fix a C)}     Γ ⊢ M : Q
---------------------------------------------------
Γ ⊢ (unwrap M) : E{[(fix a C)/a]C}

```

where `E` is an eliminiation context, defined by:

```
E ::= • | [ E A ]
```
where `A` is a type expression. The idea is that `E{C}` denotes the result of substituting `C` for the unique hole, •, in `E`.

For example, in a system with builtin products and coproducts we could define the type `P` of perfect binary trees as:

```
P = [ (fix X (lam a (type) (a + [X (a * a)]))) t ]
  = [• t]{(fix x (lam a (type (a + [X (a * a)]))))}  
```

and then, using the proposed `wrap` and `unwrap` rules, we can define constructor functions `leaf` and `node`. (TODO: write all that out). 



