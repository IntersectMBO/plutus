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
{
  description = "Plutus Core - The Scripting Language for Cardano";

  # The flake inputs will be accessible by name in each nix file like so:
  # { inputs, cell }: inputs.nixpkgs, inputs.haskell-nix
  inputs = {
    nixpkgs = {
      url = "github:NixOS/nixpkgs/34e4df55664c24df350f59adba8c7a042dece61e";
    };
    std = {
      url = "github:divnix/std";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    haskell-nix = {
      url = "github:input-output-hk/haskell.nix";
      inputs = {
        hackage.follows = "hackage-nix";
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
    # cardano-repo-tool = {
    #   url = "github:input-output-hk/cardano-repo-tool";
    #   flake = false;
    # };
    # gitignore-nix = {
    #   url = "github:hercules-ci/gitignore.nix";
    #   flake = false;
    # };
    # haskell-language-server = {
    #   # Pinned to a release
    #   url = "github:haskell/haskell-language-server?ref=1.7.0.0";
    #   flake = false;
    # };
    # iohk-nix = {
    #   url = "github:input-output-hk/iohk-nix";
    #   flake = false;
    # };
    # pre-commit-hooks-nix = {
    #   url = "github:cachix/pre-commit-hooks.nix";
    #   flake = false;
    # };
  };

  # The flake outputs are managed by std.
  outputs = inputs:

    # The growOn function accepts a first "soil" argument, defining the organelles.
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
        #   haskell
        #     Develop and build all haskell components
        #   toolchain
        #     Common tools and functions shared across multiple cells
        cellsFrom = ./nix;

        # Each cell contains arbitrary "organelles".
        # Each organelle must be either:
        #   A nix file named after the organelle
        #   A directory named after the organelle and containing a default.nix
        # Organelles have types.
        # Not all cells have the same organelles.
        # All organelles belong in a cell.
        #
        # In this repository we have five organelles, listed below with their type:
        #   devshells :: devshells
        #     Development shells available via nix develop
        #   packages :: installables
        #     Packages available via nix build
        #   devshellProfiles :: functions
        #     Building blocks for devshells, not exposed by the flake
        #   scripts :: functions
        #     Bash scripts simplifying or automating a variety of tasks
        #     Generally these are available as commands inside the development shell
        #     These are very repository specific, and are not exposed by the flake
        #   library :: functions
        #     Functions and values shared across the current cell
        #     These are very repository specific, and are not exposed by the flake
        #
        # std provides a TUI to interact with the organelles.
        # Available interactions are determined by the organelle's type.
        # Because this repository does not use the TUI, the type is actually irrelevant.
        organelles = [
          (inputs.std.devshells "devshells")
          (inputs.std.installables "packages")
          (inputs.std.functions "devshellProfiles")
          (inputs.std.functions "scripts")
          (inputs.std.functions "library")
        ];
      }

      # The growOn function will then accept an arbitrary number of attrs.
      # This is where we translate cells and organelles into a standard
      # nix flake outputs attrs.
      #
      # This is where we also decide which cells and which organelles will
      # make it into the flake. To exclude stuff from the flake, we simply
      # do not "harvest" it.
      #
      # The attrs will be recursively merged in the order in which they appear.
      {
        # Here we say that we want the devshells organelle of the doc cell
        # (which contains a number of shell-able derivations) to be exposed
        # by the flake and accessible via nix develop.
        devShells = inputs.std.harvest inputs.self [ "doc" "devshells" ];

        # Here we say that we want the packages organelle of the doc cell
        # (which contains a number of buildable derivations) to be exposed
        # by the flake and accessible via nix build (or nix run).
        packages = inputs.std.harvest inputs.self [ "doc" "packages" ];
      }
      {
        # The devshells inside the haskell cells will be added to the ones
        # already harvested from the doc shell. Same for packages.
        devShells = inputs.std.harvest inputs.self [ "haskell" "devshells" ];
        packages = inputs.std.harvest inputs.self [ "haskell" "packages" ];
      }
      {
        packages = inputs.std.harvest inputs.self [ "toolchain" "packages" ];
      };

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
  #     The full format is inputs.cells.<cell>.<organelle>.value
  #     e.g.: inputs.cells.doc.packages.doc-site
  #     e.g.: inputs.cells.toolchain.devshellsProfiles.common
  #     e.g.: inputs.cells.haskell.devshells.haskell-shell
  #
  #   inputs.*flakeInput*
  #     The flake inputs proper.
  #     e.g.: inputs.std
  #     e.g.: inputs.nixpkgs
  #     e.g.: inputs.sphinxcontrib-haddock
  #
  #   cell.*organelle*
  #     The cell value gives access to all its organelles:
  #     e.g.: cell.scripts.build-and-server-doc-site (only works for code in /nix/scripts)
  #       Alternatively: inputs.cells.doc.scripts.build-and-server-doc-site (works everywhere)
  #     e.g.: cell.packages.repo-root.nix (only works for code in /nix/toolchain)
  #       Alternatively: inputs.cells.toolchain.packages.repo-root (works everywhere)


  # # # # # ONE DERIVATION PER NIX FILE
  #
  # To enforce further discipline, we enact a one-derivation-per-file policy.
  # This is currently applied *without exception*.
  #
  # This means that every single nix file in this repository is either:
  # - A default.nix organelle importing and thus grouping all files in its folder
  # - A file evaluating to a single derivation
  #
  # Further, we enforce that the derivation name be equal to the file name.
  # This means that if one looks at the fully expanded structure of the cellsFrom folder,
  # one will conclude that there are exactly as many derivations as there are nix files
  # (excluding the default.nix files, which again merely act as a grouper for the organelle).
  #
  # Finally this means that for each nix file "some-fragment.nix", one can run:
  # nix (develop|build|run) .#some-fragment
  # That is unless the relevant organelle was not exposed by the flake.
  #
  # Also note that while virtually all nix files evaluate to derivations, some
  # (like the ones in the library organelle) actually evaluate to functions.
  # So it is more accurate to say that the convention is to export one nix *value* per nix file.


  # # # # # REFERENCE EXAMPLE
  #
  # As an example, consider the file /nix/doc/packages/eutxo-paper.nix:
  #
  # - /doc is the cell name
  # - /doc is accessible via cell.* from { inputs, cell } (while inside /nix/doc)
  # - /doc is accessible via inputs.cells.doc (everywhere)
  # - /packages is the organelle name
  # - /packages is accessible via cell.packages (while inside /nix/doc)
  # - /packages is accessible via inputs.cells.doc.packages (everywhere)
  # - /eutxo-paper.nix contains a *single derivation*
  # - A derivation named eutxo-paper is accessible via cell.packages.eutxo-paper
  # - And also accessible via inputs.cells.doc.packages.eutxo-paper
  # - And also buildable via nix build .#eutxo-paper
  #
  # An another example, consider the file /nix/toolchain/packages/default.nix
  #
  # - /toolchain is the cell name
  # - /toolchain is accessible via cell.* from { inputs, cell } (while inside /nix/toolchain)
  # - /toolchain is accessible via inputs.cells.toolchain (everywhere)
  # - /packages is the organelle name
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
