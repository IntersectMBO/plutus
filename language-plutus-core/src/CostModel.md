# To regenerate this file

```
$(nix-build default.nix -A haskell.projectPackages.language-plutus-core.components.benchmarks.language-plutus-core-create-cost-model)
```

# To rerun the benching data

```
rm language-plutus-core/budgeting-bench/csvs/benching.csv
$(nix-build default.nix -A haskell.projectPackages.language-plutus-core.components.benchmarks.language-plutus-core-budgeting-bench)
```