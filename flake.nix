# The flake.nix is the entrypoint of all nix code.
#
# This repository uses the standard tool https://github.com/divnix/std.
# Familiarity with std is required to be able to contribute effectively.
# While official documentation for std can be found in its GitHub, this flake
# has been thoroughly commented so as to quickstart new maintainers.
# This flake can also be used as a template for new std-based projects.
# Further documentation can be found in __std__/README.md
#
# You may want to refer to the standard glossary as you go along:
# https://divnix.github.io/std/glossary.html
{
  description = "Plutus Core";

  # TODO(std) these are the old inputs, remove once the new inputs are fully migrated.
  inputs = {
    __old__nixpkgs = {
      type = "github";
      owner = "NixOS";
      repo = "nixpkgs";
      ref = "nixpkgs-unstable";
      flake = false;
    };
    __old__haskell-nix = {
      url = "github:input-output-hk/haskell.nix";
      flake = false;
    };
    __old__cardano-repo-tool = {
      url = "github:input-output-hk/cardano-repo-tool";
      flake = false;
    };
    __old__gitignore-nix = {
      url = "github:hercules-ci/gitignore.nix";
      flake = false;
    };
    __old__hackage-nix = {
      url = "github:input-output-hk/hackage.nix";
      flake = false;
    };
    __old__iohk-nix = {
      url = "github:input-output-hk/iohk-nix";
      flake = false;
    };
    __old__pre-commit-hooks-nix = {
      url = "github:cachix/pre-commit-hooks.nix";
      flake = false;
    };

    # TODO(std) these are the new inputs: remove this comment once the old inputs are truly gone.
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
    CHaP = {
      url = "github:input-output-hk/cardano-haskell-packages?ref=repo";
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
    # TODO(std) update to latest version to fix:
    # warning: String 'configureFlags' is deprecated and will be removed in release 23.05.
    iohk-nix = {
      url = "github:input-output-hk/iohk-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    tullia = {
      url = "github:input-output-hk/tullia";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  # The flake outputs are managed by std.
  outputs = inputs:

    # The growOn function takes care of producing the flake outputs.
    inputs.std.growOn
      {

        # Boilerplate
        inherit inputs;

        # All nix files will reside inside this folder, no exception.
        # Each subfolder of cellsFrom is a "cell".
        # Cell names are arbitrary; a cell name is its folder name.
        # Cells are for highest-level organization and grouping of nix code.
        #
        # In this repository we have four cells:
        #   automation
        #     Hydra jobsets and GHA tasks
        #   cloud
        #     Cicero tasks
        #     (top comment in pipelines.nix explains automation and cloud separation)
        #   doc
        #     Develop and build all the documentation artifacts
        #   plutus
        #     Develop and build all haskell components
        #   toolchain
        #     Common tools and functions shared across multiple cells
        cellsFrom = ./__std__/cells;

        # Each cell contains "cell blocks".
        # Block names are arbitrary.
        # Each block can be thought of as providing a "feature" to its cell.
        # Cell blocks have types.
        # Each cell block must be either:
        #   A nix file named after the cell block
        #   A directory named after the cell block and containing a default.nix
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
        #   ciJobs :: installables
        #     Jobsets for our Hydra and Cicero CI
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
          (inputs.std.installables "ciJobs")
          (inputs.tullia.tasks "pipelines")
          (inputs.std.functions "actions")
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
        # Here we say that we want the "devshells" cell block of the doc cell
        # (which contains a number of shell-able derivations) to be exposed
        # by the flake and accessible via nix develop.
        devShells = inputs.std.harvest inputs.self [ "doc" "devshells" ];

        # Here we say that we want the "packages" cell block of the doc cell
        # (which contains a number of buildable derivations) to be exposed
        # by the flake and accessible via nix build (or nix run).
        packages = inputs.std.harvest inputs.self [ "doc" "packages" ];
      }
      {
        packages = inputs.std.harvest inputs.self [ "doc" "scripts" ];
      }
      {
        # The devshells inside the plutus cell will be added to the ones
        # already harvested from the doc shell. Same for packages.
        devShells = inputs.std.harvest inputs.self [ "plutus" "devshells" ];
        packages = inputs.std.harvest inputs.self [ "plutus" "packages" ];
      }
      {
        ciJobs = inputs.std.harvest inputs.self [ "automation" "ciJobs" ];
        packages = inputs.std.harvest inputs.self [ "automation" "ciJobs" ];
      }
      {
        packages = inputs.std.harvest inputs.self [ "toolchain" "packages" ];
      }
      {
        packages = inputs.std.harvest inputs.self [ "toolchain" "scripts" ];
      }
      (inputs.tullia.fromStd {
        actions = inputs.std.harvest inputs.self [ "cloud" "actions" ];
        tasks = inputs.std.harvest inputs.self [ "cloud" "pipelines" ];
      });

  nixConfig = {
    extra-substituters = [
      "https://cache.iog.io"
      "https://hydra.iohk.io"
    ];
    extra-trusted-public-keys = [
      "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ="
    ];
    allow-import-from-derivation = true;
  };
}
