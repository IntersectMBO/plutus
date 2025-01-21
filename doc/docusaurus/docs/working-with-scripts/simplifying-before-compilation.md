---
sidebar_position: 22
---

# Simplifying Code Before Compilation

Much like in regular Haskell, simplifying or expanding certain Plutus Tx code before compilation can make it more efficient.

As an example, suppose you want to call `PlutusTx.List.tail` on a list `n` times in Plutus Tx.
You can implement it using a fold:

```haskell
ntails :: Integer -> [a] -> [a]
ntails =
  PlutusTx.List.foldl
    (\acc _ -> PlutusTx.List.tail . acc)
    id
    (PlutusTx.replicate n ())
```

This works, but if the value of `n` is known statically, say `n = 5`, it may be better to use the following direct implementation:

```haskell
tails5 :: [a] -> [a]
tails5 =
  PlutusTx.List.tail
    . PlutusTx.List.tail
    . PlutusTx.List.tail
    . PlutusTx.List.tail
    . PlutusTx.List.tail
```

It may cause the script to increase in size if `n` is large, but this has less execution overhead, so the script will be cheaper to execute.

Even if `n` is not known statically, you can still take advantage of `tails5`, and perform `ntails` 5 elements at a time, much like [loop unrolling](https://en.wikipedia.org/wiki/Loop_unrolling):


```haskell
ntails :: Integer -> [a] -> [a]
ntails n
  | n >= 5 = nTails (n - 5) . tails5
  | otherwise =
      PlutusTx.List.foldl
        (\acc _ -> PlutusTx.List.tail . acc)
        id
        (PlutusTx.replicate n ())
```

You can write code like `tails5` by hand, but in more complex cases, you can instead use standard Haskell techniques for generating and manipulating source code, such as Template Haskell and GHC plugins.
After all, Plutus Tx is a subset of Haskell.

## Template Haskell

The most common method to programmatically generate code like `tails5` is through Template Haskell.
The following `ntailsTH` function generates a Template Haskell expression for applying `tail` `n` times, for any `n` that is statically known:

```haskell
ntailsTH :: forall a. Int -> TH.Code TH.Q ([a] -> [a])
ntailsTH n =
  Data.List.foldl'
    (\acc _ -> [|| PlutusTx.tail . $$acc ||])
    [|| id ||]
    (Data.List.replicate n ())
```

It's worth noting that `foldl'` and `replicate` are executed in Haskell for constructing the expression (rather than being compiled to UPLC), so we can use the ones in `Data.List` rather than `PlutusTx.List` (though the latter also works).

Then we can write `tails5` as

```haskell
tails5 :: [a] -> [a]
tails5 = $$(ntailsTH 5)
```

Since this is nothing but standard Template Haskell usage, we'll keep it concise here.
Some good resources to learn more about Template Haskell include the [Template Haskell page on HaskellWiki](https://wiki.haskell.org/Template_Haskell) (which has links to further resources), [Template Haskell tutorial](https://markkarpov.com/tutorial/th) by Mark Karpov, and [Introduction to Template Haskell](https://serokell.io/blog/introduction-to-template-haskell) by Heitor Toledo Lassarote de Paula.

## GHC Plugins

If you need something even more powerful and flexible than Template Haskell, you can write your own GHC plugin to customize the transformation and compilation of certain parts of your code.
However, this is a more advanced tool with greater complexity, which is further compounded by GHC's unstable API, making it difficult to support multiple major GHC versions.
You should rarely need to do this, as Template Haskell should meet most requirements.

If you do decide to write your own GHC plugin, keep in mind that the Plutus Tx compiler is also a GHC plugin, so be careful of the orders in which the two plugins are invoked, especially since [the order has changed since GHC 9.4](https://gitlab.haskell.org/ghc/ghc/-/issues/17884).

Finally, keep in mind that doing what's described in this page is not always desirable, since although it reduces script execution costs, it often increases script sizes.
For Plutus scripts, size is a much more valuable resource than for general-purpose programs, since Cardano has strict script size and transaction size limits.
