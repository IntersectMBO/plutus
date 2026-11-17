# Recursive Data with a detached specification

`OnChain.hs` defines a recursive `Tree`, a validator accepting trees whose leaves
sum to seven, and a helper that mirrors the tree. `FormalSpec.hs` imports those
bindings and contains the UAL annotations. `Main.hs` compiles both entry points,
uses `deriveRecursiveDefinitions` to collect a finite definition graph, and
writes the blueprint, assurance and checking contexts.

The validator's Tree parameter is a blueprint reference. The helper's Tree input
and result reference assurance-local `definitions`. References are retained,
including back-edges; there is no fixed-depth expansion. Helper interfaces copy
the definitions into the digest-bound checking context. Both kinds of recursive
input remain raw Data in Lean so malformed inputs can be checked explicitly.

The example verifies four claims: leaf acceptance, nested-tree sum acceptance,
exact mirroring of a nested tree, and rejection of a bare integer. The first three
quantify over integer values at fixed tree shapes. They are not arbitrary-depth
termination theorems. The runner also executes an accepted tree and rejects stale
definitions, alias cycles, missing definitions and an intentionally false claim.

```sh
cabal build --project-file=cabal.assurance.project docusaurus-examples:exe:example-ual-recursive
# From PlutusCoreBlaster, using the shared pinned Blaster and compatible Z3:
lake env python3 Tests/BlueprintVerify/run_recursive.py /path/to/example-ual-recursive /path/to/results
```

For mutually recursive Haskell types, derive the Data/schema instances together
in one Template Haskell splice, then use `deriveRecursiveDefinitions` with the
root types. Existing `deriveDefinitions` behavior is retained for custom `Unroll`
instances. Opaque custom types can provide a finite list through `definitionsFor`.
The cycle-aware generic derivation applies to concrete types with a finite type
graph; it does not describe infinitely expanding non-regular type families.
