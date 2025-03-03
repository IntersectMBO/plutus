{ inputs, system }:

let
  inherit (inputs) self;

  pkgs = import ./pkgs.nix
    { inherit inputs system; };

  inherit (pkgs) lib;

  utils = import ./utils.nix
    { inherit lib; };

  build-latex = import ./build-latex.nix
    { inherit pkgs; };

  r-with-packages = import ./r-with-packages.nix
    { inherit pkgs; };

  agda-with-stdlib = import ./agda-with-stdlib.nix
    { inherit pkgs lib; };

  build-latex-doc = import ./build-latex-doc.nix
    { inherit pkgs lib agda-with-stdlib build-latex; };

  unraveling-recursion-paper = import ./unraveling-recursion-paper.nix
    { inherit self pkgs lib build-latex agda-with-stdlib; };

  latex-documents = import ./latex-documents.nix
    { inherit self build-latex-doc; };

  metatheory-site = import ./metatheory-site.nix
    { inherit inputs self pkgs lib agda-with-stdlib; };

  hydra-required-job = utils.makeHydraRequiredJob
    { inherit self pkgs; };

  project = import ./project.nix
    { inherit inputs pkgs lib agda-with-stdlib r-with-packages; };

  mkShell = project: import ./shell.nix
    { inherit inputs pkgs lib project agda-with-stdlib r-with-packages; };

  exposed-haskell-packages = {
    plutus-core-test = project.flake'.packages."plutus-core:test:plutus-core-test";
    plutus-ir-test = project.flake'.packages."plutus-core:test:plutus-ir-test";
    cardano-constitution-test = project.flake'.packages."cardano-constitution:test:cardano-constitution-test"; # editorconfig-checker-disable-line
    cost-model-budgeting-bench = project.flake'.packages."plutus-core:exe:cost-model-budgeting-bench"; # editorconfig-checker-disable-line
  };

  static-haskell-packages = {
    musl64-pir = project.projectCross.musl64.hsPkgs.plutus-executables.components.exes.pir;
    musl64-plc = project.projectCross.musl64.hsPkgs.plutus-executables.components.exes.plc;
    musl64-uplc = project.projectCross.musl64.hsPkgs.plutus-executables.components.exes.uplc;
    musl64-plutus = project.projectCross.musl64.hsPkgs.plutus-core.components.exes.plutus;
  };

  extra-artifacts =
    { inherit unraveling-recursion-paper; } //
    { inherit metatheory-site; } //
    (latex-documents);

  project-variants-hydra-jobs = {
    ghc810 = (project.flake { }).hydraJobs.ghc810;
    ghc96 = (project.flake { }).hydraJobs.ghc96;
    ghc98 = (project.flake { }).hydraJobs.ghc98;
    ghc910 = (project.flake { }).hydraJobs.ghc910;
  };

  project-variants-roots-and-plan-nix = {
    ghc810.roots = project-variants-hydra-jobs.ghc810.roots;
    ghc810.plan-nix = project-variants-hydra-jobs.ghc810.plan-nix;
    ghc96.roots = project-variants-hydra-jobs.ghc96.roots;
    ghc96.plan-nix = project-variants-hydra-jobs.ghc96.plan-nix;
    ghc98.roots = project-variants-hydra-jobs.ghc98.roots;
    ghc98.plan-nix = project-variants-hydra-jobs.ghc98.plan-nix;
    ghc910.roots = project-variants-hydra-jobs.ghc910.roots;
    ghc910.plan-nix = project-variants-hydra-jobs.ghc910.plan-nix;
  };

  packages =
    exposed-haskell-packages //
    static-haskell-packages //
    extra-artifacts;

  devShells =
    (non-profiled-shells) //
    { profiled = mkShell project.projectVariants.profiled; };

  non-profiled-shells = rec {
    default = ghc96;
    ghc810 = mkShell project.projectVariants.ghc810;
    ghc96 = mkShell project.projectVariants.ghc96;
    ghc98 = mkShell project.projectVariants.ghc98;
    ghc910 = mkShell project.projectVariants.ghc910;
  };

  nested-ci-jobs = {
    "x86_64-linux" =
      (project-variants-hydra-jobs) //
      (packages) //
      { devShells = non-profiled-shells; } //
      { required = hydra-required-job; };
    "x86_64-darwin" =
      (project-variants-hydra-jobs) //
      { devShells = non-profiled-shells; } //
      { required = hydra-required-job; };
    "aarch64-linux" =
      { };
    "aarch64-darwin" =
      (project-variants-roots-and-plan-nix) //
      { devShells = non-profiled-shells; } //
      { required = hydra-required-job; };
  };

  flattened-ci-jobs = utils.flattenDerivationTree ":" nested-ci-jobs;

  ciJobs = utils.flattenDerivationTree ":" nested-ci-jobs.${system};

  checks = ciJobs;

  hydraJobs = ciJobs;

  __internal = {
    inherit pkgs;
    inherit project;
    inherit agda-with-stdlib;
    inherit r-with-packages;
    inherit build-latex-doc;
    inherit build-latex;
    inherit extra-artifacts;
    inherit static-haskell-packages;
    inherit exposed-haskell-packages;
    inherit flattened-ci-jobs;
    inherit nested-ci-jobs;
  };

in

{
  inherit __internal;

  inherit packages;
  inherit devShells;
  inherit checks;
  inherit hydraJobs;
}
