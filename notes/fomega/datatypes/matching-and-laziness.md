# Scott-encoding and matching
 
When we create a Scott-encoded datatype we conceptually create a type that
acts as a reified pattern-matcher: it takes functions implementing each branch
of the match, and then returns a value corresponding to the resul of the match.

For example, to match against a boolean you would write (in Haskell):
```
case bool of
    True -> a
    False -> b
```

The Scott-encoded equivalent of `Bool` is then `forall r . r -> r -> r`, and you would
write the match as:
```
bool {A} a b
```

# Lazy matching

However, matches done in this way are *strict* in a way that they usually aren't
even in strict languages. `true {A} a (error b)` is `error`, because all the arguments
to a function are evaluated before calling the funciton, violating our intuition
that the second branch shouldn't be evaluated.

You can fix this in two ways. The first is to observe that we can instantiate `r` to
whatever we want, so we can instead write
```
(true {() -> A} (() -> a) (() -> error b))()
```
and then everything is fine. This amounts to the user saying that they want a lazy 
match in this case. This has the advantage of allowing you to still do
strict matches when you want to, and closely following the Scott encoding.

Alternatively, you can bake the laziness into the type of booleans themselves, and
define `Boolean` as `forall r. (() -> r) -> (() -> r) -> r`. This way you can't 
accidentally do a strict match.

# Booleans in the spec

Booleans appear as the result type of some builtin operations in the spec, so we need to
decide how we're going to represent them there. 
