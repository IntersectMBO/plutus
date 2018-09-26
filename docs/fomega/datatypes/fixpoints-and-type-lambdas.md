When defining a polymorphic datatype such as `List`, there are two ways
to do it:
```
\a :: * . fix listA . forall r . r -> (a -> listA -> r) -> r
fix list . \a :: * . forall r . r -> (a -> list a -> r) -> r
```
In the first case we fix over a type variable of kind `*`, conceptually `List a`; 
whereas in the second we fix over a type variable of kind `* -> *`, conceptually `List`.

Now that we can fix over types of arbitrary kind, these are both perfectly valid.

However, the second approach *also* allows us to define non-uniform
datatypes in the same style, e.g. we can do perfect binary trees as:
```
fix ptree . \a :: * . forall r . r -> (ptree (pair a) -> r) -> r
```

The second approach also has the benefit that it reads somewhat more
intuitively as constructing a recursive type *constructor*.

For these reasons and to be consistent, we typically prefer 
fixpoints-outside-type-lambdas even when defining uniform datatypes.
