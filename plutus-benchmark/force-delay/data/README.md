`nested-0-n.flat` contains simple nested forces and delays.

For example, when `n = 3`:

```
force (force (force (delay (delay (delay (\a -> a))))))
```

`nested-i-n.flat`  (`i >= 1`) contains nested forces and delays, where each delayed term
is a lambda with `i` arg(s), and each `force` is followed by `i` applications.

For example, when `i = 1` and `n = 3`:

```
force
  (force
    (force
      (delay (\a1 -> delay (\a2 -> delay (\a3 -> a3))))
      1)
    2)
  3
```

When `i = 2` and `n = 3`:

```
force
  (force
    (force
      (delay (\a1 b1 -> delay (\a2 b2 -> delay (\a3 b3 -> a3))))
      1
      1)
    2
    2)
  3
  3
```
