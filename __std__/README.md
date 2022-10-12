# Nix Code Maintenance Guide

This readme provides documentation for the nix code.

The target audience includes current and future maintainers.

Start with the comments inside the [flake](../flake.nix) then continue reading here.

## The standard format of nix files 

Note how *every single nix file* in this repository (with the exception
of `flake.nix`) has the same format:
```
{ inputs, cell }: ...
```
**There is no escaping this**.

A description of the arguments follows:

- `inputs.self`\
  This is a path pointing to the top-level of the repository.\
  It is the *only* way to reference source files inside the repository.\
  Example: `{ src = inputs.self + /plutus-core-spec; }`

- `inputs.cells`\
  Provides access to all cells.\
  Remember that a cell is named after its folder.\
  The full format is: `inputs.cells.<cell>.<cell-block>.value`.\
  Examples:
  - `inputs.cells.doc.packages.read-the-docs-site`
  - `inputs.cells.toolchain.devshellsProfiles.common`
  - `inputs.cells.plutus.devshells.plutus-shell`

- `inputs.<flake-input>`\
  The flake inputs proper.\
  Examples: `inputs.std`, `inputs.nixpkgs`, `inputs.sphinxcontrib-haddock`

- `cell.<cell-block>`\
  Provides access to the cell's blocks.\
  This is a shorthand for `inputs.cells.<cell>.<cell-block>`, where `<cell>` evaluates to the cell housing this nix file.\
  Examples:
  - `cell.scripts.serve-read-the-docs-site` only works for code in `/cells/doc`\
    Alternatively `inputs.cells.doc.scripts.serve-read-the-docs-site` works everywhere
  - `cell.packages.repo-root` only works for code in `/cells/toolchain`\
    Alternatively `inputs.cells.toolchain.packages.repo-root` works everywhere

## One derivation per nix file

To enforce further discipline, we enact a one-derivation-per-file policy.

This is currently applied *without exception*.

This means that every single nix file in this repository is either:

- A `default.nix` cell block importing and thus grouping all files in its folder
- A file evaluating to a single derivation

Further, we enforce that the nix fragment name be equal to the file name.

This means that if one looks at the fully expanded structure of the `cellsFrom` folder, one will conclude that there are exactly as many fragments as there are nix files (excluding the `default.nix` files, which again merely act as a grouper for the cell block).

Finally this means that for each nix file `some-fragment.nix`, one can run:
`nix (develop|build|run) .#some-fragment`

That is unless the relevant cell block was not exposed as a flake output.

Note however that what stated above doesn't hold for the `library`, `devshellProfiles`, `hydraJobs` cell blocks.

Indeed the `library` block hosts nix files that evaluate to functions, literal values, or more complex attribute sets; `devshellProfiles` contains building blocks (functions) for `devshells`; `hydraJobs` contains hydra jobsets, which are nested attributes of derivations.

## Reference example

As an example, consider the file `__std__/cells/doc/packages/eutxo-paper.nix`:

- `__std__/cells` is the `cellsFrom` value in `flake.nix`
- `/doc` is the cell name
- `/doc/*` are accessible via `cell.*` from `{ inputs, cell }` (while inside `cells/doc`)
- `/doc/*` are accessible via `inputs.cells.doc.*` (everywhere)
- `/packages` is the cell block name
- `/packages/*` are accessible via `cell.packages.*` (while inside `cells/doc`)
- `/packages/*` are accessible via `inputs.cells.doc.packages.*` (everywhere)
- `/eutxo-paper.nix` contains a *single derivation*
- `eutxo-paper` is the name of the flake fragment
- A derivation named `eutxo-paper` is accessible via `cell.packages.eutxo-paper` (while inside `cells/doc`)
- And also accessible via `inputs.cells.doc.packages.eutxo-paper` (everywhere)
- And also buildable via `nix build .#eutxo-paper`

As another example, consider the file `__std__/cells/toolchain/packages/default.nix`

- `__std__/cells` is the `cellsFrom` value in `flake.nix`
- `/toolchain` is the cell name
- `/toolchain/*` are accessible via `cell.*` from `{ inputs, cell }` (while inside `cells/toolchain`)
- `/toolchain/*` are accessible via `inputs.cells.toolchain.*` (everywhere)
- `/packages` is the cell block name
- `/packages/*` are accessible via `cell.packages.*` (while inside `cells/toolchain`)
- `/packages/*` are accessible via `inputs.cells.toolchain.packages.*` (everywhere)
- `/default.nix` imports every file in its directory
- `/default.nix` contains a derivation for each file in its directory
- Each attrs field in `/default.nix` is named after the file it imports (minus the `.nix`)


## Migration Checklist 

Migration to `std` will be 100% complete once all these are done:

- Replace all occurrences of `__std__` to `nix`
- Remove *every* nix files not in `nix` 
- Do all remaining `TODO(std)`s 
- Check CONTRIBUTING.adoc for references to old nix files