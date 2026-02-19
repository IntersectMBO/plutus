{ inputs, system }:

let
  inherit (inputs) self;

  pkgs = import ./pkgs.nix
    { inherit inputs system; };

  inherit (pkgs) lib;

  utils = import ./utils.nix
    { inherit lib; };

  r-with-packages = import ./r-with-packages.nix
    { inherit pkgs; };

  agda-tools = import ./agda-tools.nix
    { inherit self pkgs lib; };

  build-latex-doc = import ./build-latex-doc.nix
    { inherit pkgs lib agda-tools; };

  latex-documents = import ./latex-documents.nix
    { inherit self build-latex-doc; };

  metatheory = import ./metatheory.nix
    { inherit inputs self pkgs lib agda-tools; };

  hydra-required-job = utils.makeHydraRequiredJob
    { inherit self pkgs; };

  project = import ./project.nix
    { inherit inputs pkgs lib metatheory r-with-packages utils; };

  mkFourmolu = import ./fourmolu.nix
    { inherit pkgs lib; };

  mkShell = ghc: import ./shell.nix
    { inherit inputs pkgs lib project agda-tools metatheory r-with-packages ghc mkFourmolu; };

  exposed-haskell-packages = {
    plutus-core-test = project.flake'.packages."plutus-core:test:plutus-core-test";
    plutus-ir-test = project.flake'.packages."plutus-core:test:plutus-ir-test";
    cardano-constitution-test = project.flake'.packages."cardano-constitution:test:cardano-constitution-test"; # editorconfig-checker-disable-line
    cost-model-budgeting-bench = project.flake'.packages."plutus-core:exe:cost-model-budgeting-bench"; # editorconfig-checker-disable-line
    uplc = project.flake'.packages."plutus-executables:exe:uplc";
    plc = project.flake'.packages."plutus-executables:exe:plc";
    pir = project.flake'.packages."plutus-executables:exe:pir";
    plutus = project.flake'.packages."plutus-core:exe:plutus";
    uplc-evaluator = project.flake'.packages."plutus-benchmark:exe:uplc-evaluator";
  };

  static-haskell-packages = {
    musl64-pir = project.projectCross.musl64.hsPkgs.plutus-executables.components.exes.pir;
    musl64-plc = project.projectCross.musl64.hsPkgs.plutus-executables.components.exes.plc;
    musl64-uplc = project.projectCross.musl64.hsPkgs.plutus-executables.components.exes.uplc;
    musl64-plutus = project.projectCross.musl64.hsPkgs.plutus-core.components.exes.plutus;
  };

  windows-hydra-jobs = {
    ghc96-mingsW64 = removeAttrs
      (project.projectCross.mingwW64.flake { }).hydraJobs.ghc96
      [ "devShells" ]; # Won't build on Windows
  };

  project-coverage-report =
    project.projectVariants.ghc96-coverage.projectCoverageReport;

  extra-artifacts =
    {
      inherit (metatheory) metatheory-site metatheory-agda-library;
      inherit project-coverage-report;
    }
    //
    latex-documents;

  project-variants-hydra-jobs = {
    ghc96 = (project.flake { }).hydraJobs.ghc96;
    ghc912 = (project.flake { }).hydraJobs.ghc912;
    ghc96-profiled = (project.flake { }).hydraJobs.ghc96-profiled;
    ghc912-profiled = (project.flake { }).hydraJobs.ghc912-profiled;
  };

  project-variants-roots-and-plan-nix = {
    ghc96.roots = project-variants-hydra-jobs.ghc96.roots;
    ghc96.plan-nix = project-variants-hydra-jobs.ghc96.plan-nix;
    ghc912.roots = project-variants-hydra-jobs.ghc912.roots;
    ghc912.plan-nix = project-variants-hydra-jobs.ghc912.plan-nix;
    ghc96-profiled.roots = project-variants-hydra-jobs.ghc96-profiled.roots;
    ghc96-profiled.plan-nix = project-variants-hydra-jobs.ghc96-profiled.plan-nix;
    ghc912-profiled.roots = project-variants-hydra-jobs.ghc912-profiled.roots;
    ghc912-profiled.plan-nix = project-variants-hydra-jobs.ghc912-profiled.plan-nix;
  };

  packages =
    lib.optionalAttrs pkgs.stdenv.isLinux static-haskell-packages //
    exposed-haskell-packages //
    extra-artifacts;

  # The default shell contains the agda-with-stdlib-and-metatheory package which will
  # break on `nix develop` if the .lagda files are broken. In order to escape this
  # situation we introduce a shell that doesn't contain that executable.
  metatheory-jailbreak-shell = devShells.default.overrideAttrs (attrs: {
    buildInputs =
      lib.remove metatheory.agda-with-stdlib-and-metatheory attrs.buildInputs;
    nativeBuildInputs =
      lib.remove metatheory.agda-with-stdlib-and-metatheory attrs.nativeBuildInputs;
  });

  devShells = rec {
    default = ghc96;
    ghc96 = mkShell "ghc96";
    ghc912 = mkShell "ghc912";
    ghc96-profiled = mkShell "ghc96-profiled";
    ghc912-profiled = mkShell "ghc912-profiled";
    metatheory-jailbreak = metatheory-jailbreak-shell;
  };

  nested-ci-jobs = {
    "x86_64-linux" =
      (windows-hydra-jobs) //
      (packages) //
      { ghc96 = project-variants-hydra-jobs.ghc96; } //
      { ghc912 = project-variants-hydra-jobs.ghc912; } //
      { ghc96-profiled = project-variants-hydra-jobs.ghc96-profiled; } //
      { ghc912-profiled = project-variants-hydra-jobs.ghc912-profiled; } //
      { devShells.ghc96 = devShells.ghc96; } //
      { devShells.ghc912 = devShells.ghc912; } //
      { devShells.ghc96-profiled = devShells.ghc96-profiled; } //
      { devShells.ghc912-profiled = devShells.ghc912-profiled; } //
      { devShells.metatheory-jailbreak = metatheory-jailbreak-shell; } //
      { required = hydra-required-job; };
    "x86_64-darwin" =
      { ghc96 = project-variants-hydra-jobs.ghc96; } //
      { ghc912 = project-variants-hydra-jobs.ghc912; } //
      { ghc96-profiled = project-variants-hydra-jobs.ghc96-profiled; } //
      { ghc912-profiled = project-variants-hydra-jobs.ghc912-profiled; } //
      { devShells.ghc96 = devShells.ghc96; } //
      { devShells.ghc912 = devShells.ghc912; } //
      { devShells.ghc96-profiled = devShells.ghc96-profiled; } //
      { devShells.ghc912-profiled = devShells.ghc912-profiled; } //
      { devShells.metatheory-jailbreak = metatheory-jailbreak-shell; } //
      { required = hydra-required-job; };
    "aarch64-linux" =
      { };
    "aarch64-darwin" =
      (project-variants-roots-and-plan-nix) //
      { devShells.ghc96 = devShells.ghc96; } //
      { devShells.ghc912 = devShells.ghc912; } //
      { devShells.ghc96-profiled = devShells.ghc96-profiled; } //
      { devShells.ghc912-profiled = devShells.ghc912-profiled; } //
      { devShells.metatheory-jailbreak = metatheory-jailbreak-shell; } //
      { required = hydra-required-job; };
  };

  ciJobs = utils.flattenDerivationTree ":" nested-ci-jobs.${system};

  checks = ciJobs;

  hydraJobs = ciJobs;

  __internal = {
    inherit self;
    inherit pkgs;
    inherit project;
    inherit agda-tools;
    inherit r-with-packages;
    inherit build-latex-doc;
    inherit extra-artifacts;
    inherit windows-hydra-jobs;
    inherit static-haskell-packages;
    inherit exposed-haskell-packages;
    inherit metatheory;
    inherit project-coverage-report;
  };

in

{
  inherit __internal;

  inherit packages;
  inherit devShells;
  inherit checks;
  inherit hydraJobs;
}


