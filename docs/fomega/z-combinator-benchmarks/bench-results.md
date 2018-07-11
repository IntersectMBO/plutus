We compare a fixed point operator defined directly by recursion

```haskell
fix' :: ((a -> b) -> a -> b) -> a -> b
fix' f x = (f $! fix' f) $! x
```

to the `Z` combinator defined via type-level recursion:

```haskell
newtype Rec a = In { out :: Rec a -> a }

z :: ((a -> b) -> a -> b) -> a -> b
z = \f -> let a = \r -> f (\x -> out r r $! x) in a (In a)
```

There doesn't seem to be any substantial difference between the two.
