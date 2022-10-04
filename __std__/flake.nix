# The flake.nix is the entrypoint of all nix code.
#
# This repository uses the std tool https://github.com/divnix/std.
# Familiarity with std is required to be able to contribute effectively.
# While official documentation for std can be found in its GitHub, this flake
# has been thoroughly commented so as to quickstart new maintainers.
#
# Most of what there is to know about the nix code inside this repository
# can be learned by reading this file. A second read will be needed as some
# std-specific terms may be referenced first and defined later.
# You may also refer to the glossary: https://divnix.github.io/std/glossary.html
{
  description = "Plutus Core";

  # The flake inputs will be accessible by name in each nix file like so:
  # { inputs, cell }: inputs.nixpkgs, inputs.haskell-nix
  inputs = {
    nixpkgs = {
      url = "github:NixOS/nixpkgs";
    };
    std = {
      url = "github:divnix/std";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    haskell-nix = {
      url = "github:input-output-hk/haskell.nix";
      inputs = {
        hackage.follows = "hackage-nix";
        nixpkgs.follows = "nixpkgs";
      };
    };
    hackage-nix = {
      url = "github:input-output-hk/hackage.nix";
      flake = false;
    };
    sphinxcontrib-haddock = {
      url = "github:michaelpj/sphinxcontrib-haddock";
      flake = false;
    };
    gitignore-nix = {
      url = "github:hercules-ci/gitignore.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    haskell-language-server = {
      # Pinned to a release
      url = "github:haskell/haskell-language-server?ref=1.8.0.0";
      flake = false;
    };
    pre-commit-hooks-nix = {
      url = "github:cachix/pre-commit-hooks.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    iohk-nix = {
      url = "github:input-output-hk/iohk-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  # The flake outputs are managed by std.
  outputs = inputs:

    # The growOn function accepts a first argument defining the cell blocks.
    inputs.std.growOn
      {

        # Boilerplate
        inherit inputs;

        # ALL nix files will reside inside this folder, no exception.
        # Each subfolder is a "cell".
        # Cell names are arbitrary.
        # Cells are for highest-level organization and grouping of nix code.
        #
        # In this repository we have three cells:
        #   doc
        #     Develop and build all the documentation artifacts
        #   plutus
        #     Develop and build all haskell components
        #   toolchain
        #     Common tools and functions shared across multiple cells
        cellsFrom = ./nix;

        # Each cell contains arbitrary "cell blocks".
        # Each cell block must be either:
        #   A nix file named after the cell block
        #   A directory named after the cell block and containing a default.nix
        # Cell blocks have types.
        # Not all cells have the same cell blocks.
        # All cell blocks belong in a cell.
        #
        # In this repository we have five cell blocks, listed below with their type:
        #   devshells :: devshells
        #     Development shells available via nix develop
        #   packages :: installables
        #     Packages available via nix build
        #   devshellProfiles :: functions
        #     Building blocks for devshells, not exposed to the flake
        #   scripts :: functions
        #     Bash scripts simplifying or automating a variety of tasks
        #     Generally these are available as commands inside the development shell
        #     These are very repository specific but are exposed to the flake nonetheless
        #   library :: functions
        #     Everything that is not a derivation goes here
        #     Includes functions, attrsets and simple literal values shared across cells
        #     These are not exposed to the flake
        #
        # std provides a TUI to interact with the cell blocks.
        # Available interactions are determined by the cell block's type.
        # Because this repository does not yet use the TUI, the type is mostly irrelevant.
        cellBlocks = [
          (inputs.std.devshells "devshells")
          (inputs.std.installables "packages")
          (inputs.std.functions "devshellProfiles")
          (inputs.std.functions "scripts")
          (inputs.std.functions "library")
        ];
      }

      # The growOn function will then accept an arbitrary number of "soil" attrs.
      # This is where we translate cells and cell blocks into a standard nix flake
      # outputs attrs.
      #
      # This is where we also decide which cells and which cell blocks will
      # make it into the flake. To exclude stuff from the flake, we simply
      # do not "harvest" it.
      #
      # The attrs will be recursively merged in the order in which they appear.
      {
        # Here we say that we want the devshells cell block of the doc cell
        # (which contains a number of shell-able derivations) to be exposed
        # by the flake and accessible via nix develop.
        devShells = inputs.std.harvest inputs.self [ "doc" "devshells" ];

        # Here we say that we want the packages cell block of the doc cell
        # (which contains a number of buildable derivations) to be exposed
        # by the flake and accessible via nix build (or nix run).
        packages = inputs.std.harvest inputs.self [ "doc" "packages" ];
      }
      {
        packages = inputs.std.harvest inputs.self [ "doc" "scripts" ];
      }
      {
        # The devshells inside the haskell cells will be added to the ones
        # already harvested from the doc shell. Same for packages.
        devShells = inputs.std.harvest inputs.self [ "plutus" "devshells" ];
        packages = inputs.std.harvest inputs.self [ "plutus" "packages" ];
      }
      {
        packages = inputs.std.harvest inputs.self [ "toolchain" "packages" ];
      }
      {
        packages = inputs.std.harvest inputs.self [ "toolchain" "scripts" ];
      };

  # TODO(std) move this part of the doc (which doesn't need to reference the code
  # in flake.nix) into the README or in a separate doc.

  # # # # # THE STANDARD FORMAT OF NIX FILES
  #
  # Notice how *every single nix file* in this repository (with the exception
  # of flake.nix) has the same format:
  #
  # { inputs, cell }: ...
  #
  # There is no escaping this.
  # A description of the arguments follows:
  #
  #   inputs.self
  #     This is a path pointing to the top level of the repository.
  #     It is the *only* way to reference source files inside the repository.
  #     e.g.: { src = inputs.self + /plutus-core-spec; }
  #
  #   inputs.cells
  #     Provides access to all cells.
  #     Remember that a cell is named after its folder.
  #     The full format is inputs.cells.<cell>.<cell-block>.value
  #     e.g.: inputs.cells.doc.packages.read-the-docs-site
  #     e.g.: inputs.cells.toolchain.devshellsProfiles.common
  #     e.g.: inputs.cells.haskell.devshells.haskell-shell
  #
  #   inputs.*flakeInput*
  #     The flake inputs proper.
  #     e.g.: inputs.std
  #     e.g.: inputs.nixpkgs
  #     e.g.: inputs.sphinxcontrib-haddock
  #
  #   cell.*cell block*
  #     The cell value gives access to all its cell blocks:
  #     e.g.: cell.scripts.serve-read-the-docs-site (only works for code in /nix/scripts)
  #       Alternatively: inputs.cells.doc.scripts.serve-read-the-docs-site (works everywhere)
  #     e.g.: cell.packages.repo-root.nix (only works for code in /nix/toolchain)
  #       Alternatively: inputs.cells.toolchain.packages.repo-root (works everywhere)


  # # # # # ONE DERIVATION PER NIX FILE
  #
  # To enforce further discipline, we enact a one-derivation-per-file policy.
  # This is currently applied *without exception*.
  #
  # This means that every single nix file in this repository is either:
  # - A default.nix cell block importing and thus grouping all files in its folder
  # - A file evaluating to a single derivation
  #
  # Further, we enforce that the nix fragment name be equal to the file name.
  # This means that if one looks at the fully expanded structure of the cellsFrom folder,
  # one will conclude that there are exactly as many fragments as there are nix files
  # (excluding the default.nix files, which again merely act as a grouper for the cell block).
  #
  # Finally this means that for each nix file "some-fragment.nix", one can run:
  # nix (develop|build|run) .#some-fragment
  # That is unless the relevant cell block was not exposed by the flake.
  #
  # Also note that while virtually all nix files evaluate to derivations, some
  # (like the ones in the library cell block) actually evaluate to functions.
  # So it is more accurate to say that the convention is to export one
  # (non-attribute-set!) nix value per nix file.


  # # # # # REFERENCE EXAMPLE
  #
  # As an example, consider the file /nix/doc/packages/eutxo-paper.nix:
  #
  # - /doc is the cell name
  # - /doc is accessible via cell.* from { inputs, cell } (while inside /nix/doc)
  # - /doc is accessible via inputs.cells.doc (everywhere)
  # - /packages is the cell block name
  # - /packages is accessible via cell.packages (while inside /nix/doc)
  # - /packages is accessible via inputs.cells.doc.packages (everywhere)
  # - /eutxo-paper.nix contains a *single derivation*
  # - eutxo-paper is the name of the flake fragment
  # - A derivation named eutxo-paper is accessible via cell.packages.eutxo-paper
  # - And also accessible via inputs.cells.doc.packages.eutxo-paper
  # - And also buildable via nix build .#eutxo-paper
  #
  # As another example, consider the file /nix/toolchain/packages/default.nix
  #
  # - /toolchain is the cell name
  # - /toolchain is accessible via cell.* from { inputs, cell } (while inside /nix/toolchain)
  # - /toolchain is accessible via inputs.cells.toolchain (everywhere)
  # - /packages is the cell block name
  # - /packages is accessible via cell.packages (while inside /nix/toolchain)
  # - /packages is accessible via inputs.cells.toolchain.packages (everywhere)
  # - /default.nix imports every file in its directory
  # - /default.nix contains a derivation for each file in its directory
  # - Each attrs field in /default.nix is named after the file it imports (minus the .nix)

  nixConfig = {
    extra-substituters = [
      "https://cache.iog.io"
      "https://hydra.iohk.io"
    ];
    extra-trusted-public-keys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
    ];
    allow-import-from-derivation = true;
    accept-flake-config = true;
  };
}
