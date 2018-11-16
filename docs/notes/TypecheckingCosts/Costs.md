Typechecking costs are relatively simple: we say that each reduction step

```
[ (lam x S A) B ] -> [A/x]B
```

costs 1 gas. This ensures that types which are already normalized pay nothing.
