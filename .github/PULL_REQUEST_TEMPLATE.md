<!--
Here are some checklists you may like to use. Use your judgement.

This is just a checklist, all the normative suggestions are covered in more detail in CONTRIBUTING.
-->
Pre-submit checklist:
- Branch
    - [ ] Commit sequence broadly makes sense
    - [ ] Key commits have useful messages
    - [ ] Relevant tickets are mentioned in commit messages
- PR
    - [ ] Self-reviewed the diff
    - [ ] Useful pull request description
    - [ ] Reviewer requested
- If you updated any cabal files or added Haskell packages:
    - [ ] `$(nix-build default.nix -A dev.scripts.updateMaterialized)` to update the materialized Nix files
   - [ ] Update `hie-*.yaml` files if needed
- If you changed any Haskell files:
   - [ ] `$(nix-shell shell.nix --run fix-stylish-haskell)` to fix any formatting issues
- If you changed any Purescript files:
   - [ ] `$(nix-shell shell.nix --run fix-purty)` to fix any formatting issues

Pre-merge checklist:
- [ ] Someone approved it
- [ ] Commits have useful messages
- [ ] Review clarifications made it into the code
- [ ] History is moderately tidy; or going to squash-merge
