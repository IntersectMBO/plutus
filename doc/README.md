# Plutus and Marlowe documentation site
 
This is a sphinx site. You can build it with sphinx directly (assuming you're in a `nix-shell`):

```
sphinx-build -j 4 -n . _build
```

Or you can build it with Nix at the top level, which will also build the Haddock for the project and link it in:

```
nix build -f default.nix docs.site
```
