# DevEnv & CI - Maintenance Guide & Troubleshooting

This document is intended both for maintainers of the nix code and for developers facing issues with their development environment or with the CI system.

# Troubleshooting 


<div style="background-color: #FFFF0033; padding: 5px;">

`nix develop` fails to enter the shell, `cabal build` fails when it shouldn't.

</div>

In general when facing any problem related to the nix shell or cabal failing to build when it shouldn't, the first step is to make sure you are using the latest shell from master: first exit the nix shell, then `git pull --rebase origin master`, then re-enter the nix shell (i.e. run `nix develop`). 

If that fails, you might be facing a caching issue. In that case, try this before exiting and re-entering the nix shell:

```
rm -r ~/.cabal/{store,packages} plutus-metatheory/_build dist dist-newstyle
```

<div style="background-color: #FFFF0033; padding: 5px;">

`nix develop` is updating the `flake.lock` file.
</div>

This should never happen, it is a bug in nix, and has been observed in version `2.26.1`.
Downgrade your nix installation to fix this issue. 

