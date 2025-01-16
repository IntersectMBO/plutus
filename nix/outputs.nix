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

  project = import ./project.nix
    { inherit inputs pkgs lib agda-with-stdlib r-with-packages; };

  shell = import ./shell.nix
    { inherit inputs pkgs lib project agda-with-stdlib r-with-packages; };

  profiled-shell = import ./shell.nix {
    inherit pkgs agda-with-stdlib r-with-packages;
    project = project.flake'.variants.profiled;
  };

  common-haskell-packages = {
    plutus-core-test = project.flake'.packages."plutus-core:test:plutus-core-test";
    plutus-ir-test = project.flake'.packages."plutus-core:test:plutus-ir-test";
    cardano-constitution-test = project.flake'.packages."cardano-constitution:test:cardano-constitution-test"; # editorconfig-checker-disable-line
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
    common-haskell-packages //
    static-haskell-packages //
    extra-artifacts;

  devShells = {
    default = shell;
    profiled = profiled-shell;
  };

  nested-ci-jobs = {
    "x86_64-linux" =
      (project-variants-hydra-jobs) //
      (packages) //
      { devShells.default = shell; };
    "x86_64-darwin" =
      (project-variants-hydra-jobs) //
      { devShells.default = shell; };
    "aarch64-darwin" =
      (project-variants-roots-and-plan-nix) //
      { devShells.default = shell; };
    "aarch64-linux" =
      { };
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
    inherit common-haskell-packages;
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
