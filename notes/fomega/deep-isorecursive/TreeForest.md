## The Encoding of `tree` and `forest`

How to arrive at this representation is described in great detail in the [`MutualData`](../mutual-type-level-recursion/MutualData.agda) document. The representation itself:

```
treeTag   = \(t f :: *) -> t
forestTag = \(t f :: *) -> f

-- The pattern functor of both `tree` and `forest`. Depending on how we instantiate `tag`, we can get either the pattern functor of `tree` or the one of `forest`.
treeForestF =
    \(a :: *) (rec :: (* -> * -> *) -> *) (tag :: * -> * -> *) -> all (r :: *).
        tag ((a -> rec forestTag -> r) -> r)                  -- `case` over `tree`
            (r -> (rec treeTag -> rec forestTag -> r) -> r))  -- `case` over `forest`

-- The definitions of the data types.

tree   = \(a :: *) -> ifix (treeForestF a) treeTag
forest = \(a :: *) -> ifix (treeForestF a) forestTag

-- The definitions of their constructors.

node =
    /\(a :: *) ->
    -- The `node` constructor receives an `a` and a `forest a`
    \(x : a) -> \(fr : forest a) ->
        -- and constructs a `tree` (note the `treeTag`)
        iwrap (treeForestF a) treeTag
            -- Here we encode `case`. Since `tree` has only one constructor
            -- of type `a -> forest a -> tree a`, we eliminate it with a single function
            -- of type `a -> forest a -> r`:
            (/\(r :: *) -> \(f : a -> forest a -> r) -> f x fr)

nil =
    /\(a :: *) ->
        -- The `nil` constructor does not receive anything and constructrs a `forest`
        iwrap (treeForestF a) forestTag
            -- Here we encode `case`. Since `forest` has two constructors:
            -- `nil : forest a` and `cons : tree a -> forest a -> forest a`,
            -- we eliminate them with two values of types
            -- `r` and `tree a -> forest a -> r`.
            (/\(r :: *) -> \(z : r) -> \(f : tree a -> forest a -> r) ->
                -- Since we're encoding `nil` here, we return the value that eliminates `nil`.
                z)

cons =
    /\(a :: *) ->
    -- The `cons` constructor receives a `tree` and a `forest`
    \(tr : tree a) -> \(fr : forest a) ->
        -- and constructs a `forest`
        iwrap (treeForestF a) forestTag
            -- Same reasoning as in the `nil` example above
            (/\(r :: *) -> \(z : r) -> \(f : tree a -> forest a -> r) ->
                -- Since we're encoding `cons` here, we return the value that eliminates `cons`.
                f tr fr)
```

This encoding is not what we use in practice, because manipulating pattern functors is very inconvenient to the user that generates Plutus Core and the user that writes it directly. Instead, we have a representation that doesn't expose any pattern functors to the user and exposes some higher-level primitives instead. It is more complicated though, so we show the simpler version here.

But in any case this is a true encoding of a family of mutually recursive data types and there is no mention of spines whatsoever. This encoding works in both the `ifix` and the head-spine form settings without any additional tricks. We only need to provide these simple definitions in the head-spine form setting:

```
ifix  =  \(f :: (k -> *) -> k -> *) (a :: k) ->                        Spines.fix  f [a]
iwrap = /\(f :: (k -> *) -> k -> *) (a :: k) -> \(t : f (ifix f) a) -> Spines.wrap f [a] t
```

And nothing else is required. This proves that the topics of mutual type-level recursion and ways to get higher-kinded `fix` are completely orthogonal and shouldn't be conflated.
