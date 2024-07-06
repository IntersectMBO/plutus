{ repoRoot, inputs, pkgs, system, lib }:

let
  project = repoRoot.nix.project;

  ghc96 = project.variants.ghc96;
  ghc96-mingwW64 = project.variants.ghc96.cross.mingwW64;
  ghc96-musl64 = project.variants.ghc96.cross.musl64;
  ghc96-profiled = project.variants.ghc96-profiled;
  ghc98 = project.variants.ghc98;
  ghc810 = project.variants.ghc810;
  ghc910 = project.variants.ghc910;
in

[
  {
    inherit (project) cabalProject;

    devShells.default = ghc96.devShell;
    devShells.profiled = ghc96-profiled.devShell;
    devShells.ghc96 = ghc96.devShell;
    devShells.ghc810 = ghc810.devShell;
    devShells.ghc98 = ghc98.devShell;
    devShells.ghc910 = ghc910.devShell;

    packages = ghc96.packages;
    apps = ghc96.apps;
    checks = ghc96.checks;

    latex-documents = repoRoot.nix.latex-documents;

    hydraJobs.required = lib.iogx.mkHydraRequiredJob { };
  }

  {
    packages.plutus-metatheory-site = repoRoot.nix.plutus-metatheory-site;
    packages.pre-commit-check = ghc96.pre-commit-check;
  }

  (lib.optionalAttrs (system == "x86_64-linux" || system == "x86_64-darwin")
    {
      hydraJobs.plutus-metatheory-site = repoRoot.nix.plutus-metatheory-site;

      hydraJobs.ghc96 = ghc96.hydraJobs;
      hydraJobs.ghc810 = ghc810.hydraJobs;
      hydraJobs.ghc98 = ghc98.hydraJobs;
      hydraJobs.ghc910 = ghc910.hydraJobs;
    })

  (lib.optionalAttrs (system == "x86_64-linux")
    {
      hydraJobs.latex-documents = repoRoot.nix.latex-documents;
      hydraJobs.pre-commit-check = ghc96.pre-commit-check;

      hydraJobs.mingwW64.ghc96 = ghc96-mingwW64.hydraJobs;

      hydraJobs.musl64.ghc96.pir = ghc96-musl64.cabalProject.hsPkgs.plutus-core.components.exes.pir;
      hydraJobs.musl64.ghc96.plc = ghc96-musl64.cabalProject.hsPkgs.plutus-core.components.exes.plc;
      hydraJobs.musl64.ghc96.uplc = ghc96-musl64.cabalProject.hsPkgs.plutus-core.components.exes.uplc; # editorconfig-checker-disable-line
      hydraJobs.musl64.ghc96.plutus = ghc96-musl64.cabalProject.hsPkgs.plutus-core.components.exes.plutus; # editorconfig-checker-disable-line
    })

  (lib.optionalAttrs (system == "aarch64-darwin")
    {
      # Plausibly if things build on x86 darwin then they'll build on aarch darwin.
      # Se we only build roots and devshells on aarch to avoid overloading the builders.
      # Note: We can't build the 9.6 shell on aarch64-darwin
      # because of https://github.com/well-typed/cborg/issues/311
      hydraJobs.ghc810.devShell = ghc810.devShell;
      hydraJobs.ghc96.devShell = ghc96.devShell;
      hydraJobs.ghc98.devShell = ghc98.devShell;
      hydraJobs.ghc910.devShell = ghc910.devShell;

      hydraJobs.ghc810.roots = ghc810.hydraJobs.roots;
      hydraJobs.ghc810.plan-nix = ghc810.hydraJobs.plan-nix;

      hydraJobs.ghc96.roots = ghc96.hydraJobs.roots;
      hydraJobs.ghc96.plan-nix = ghc96.hydraJobs.plan-nix;

      hydraJobs.ghc98.roots = ghc98.hydraJobs.roots;
      hydraJobs.ghc98.plan-nix = ghc98.hydraJobs.plan-nix;

      hydraJobs.ghc910.roots = ghc910.hydraJobs.roots;
      hydraJobs.ghc910.plan-nix = ghc910.hydraJobs.plan-nix;
    })
]
