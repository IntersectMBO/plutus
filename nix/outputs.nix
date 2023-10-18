{ repoRoot, inputs, pkgs, system, lib }:

let
  project = repoRoot.nix.project;

  ghc92 = project.variants.ghc92;
  ghc92-mingwW64 = project.variants.ghc92.cross.mingwW64;
  ghc92-musl64 = project.variants.ghc92.cross.musl64;
  ghc92-profiled = project.variants.ghc92-profiled;
  ghc96 = project.variants.ghc96;
  ghc810 = project.variants.ghc810;

in

[
  {
    inherit (project) cabalProject;

    devShells.default = ghc92.devShell;
    devShells.profiled = ghc92-profiled.devShell;
    devShells.ghc92 = ghc92.devShell;
    devShells.ghc810 = ghc810.devShell;
    devShells.ghc96 = ghc96.devShell;

    packages = ghc92.packages;
    apps = ghc92.apps;
    checks = ghc92.checks;

    latex-documents = repoRoot.nix.latex-documents;

    hydraJobs.required = lib.iogx.mkHydraRequiredJob { };
  }

  {
    packages.plutus-metatheory-site = repoRoot.nix.plutus-metatheory-site;
    packages.pre-commit-check = ghc92.pre-commit-check;
    packages.read-the-docs-site = ghc92.read-the-docs-site;
    packages.combined-haddock = ghc92.combined-haddock;
  }

  (lib.optionalAttrs (system == "x86_64-linux" || system == "x86_64-darwin")
    {
      hydraJobs.plutus-metatheory-site = repoRoot.nix.plutus-metatheory-site;

      hydraJobs.ghc810 = ghc810.hydraJobs;
      hydraJobs.ghc92 = ghc92.hydraJobs;
      hydraJobs.ghc96 = ghc96.hydraJobs;
    })

  (lib.optionalAttrs (system == "x86_64-linux")
    {
      hydraJobs.latex-documents = repoRoot.nix.latex-documents;
      hydraJobs.read-the-docs-site = ghc92.read-the-docs-site;
      hydraJobs.pre-commit-check = ghc92.pre-commit-check;
      hydraJobs.combined-haddock = ghc92.combined-haddock;

      hydraJobs.mingwW64.ghc92 = ghc92-mingwW64.hydraJobs;

      hydraJobs.musl64.ghc92.pir = ghc92-musl64.cabalProject.hsPkgs.plutus-core.components.exes.pir;
      hydraJobs.musl64.ghc92.plc = ghc92-musl64.cabalProject.hsPkgs.plutus-core.components.exes.plc;
      hydraJobs.musl64.ghc92.uplc = ghc92-musl64.cabalProject.hsPkgs.plutus-core.components.exes.uplc; # editorconfig-checker-disable-line
      hydraJobs.musl64.ghc92.debugger = ghc92-musl64.cabalProject.hsPkgs.plutus-core.components.exes.debugger; # editorconfig-checker-disable-line
    })

  (lib.optionalAttrs (system == "aarch64-darwin")
    {
      # Plausibly if things build on x86 darwin then they'll build on aarch darwin.
      # Se we only build roots and devshells on aarch to avoid overloading the builders.
      # Note: We can't build the 9.6 shell on aarch64-darwin
      # because of https://github.com/well-typed/cborg/issues/311
      hydraJobs.ghc810.devShell = ghc810.devShell;
      hydraJobs.ghc92.devShell = ghc92.devShell;

      hydraJobs.ghc810.roots = ghc810.hydraJobs.roots;
      hydraJobs.ghc810.plan-nix = ghc810.hydraJobs.plan-nix;

      hydraJobs.ghc92.roots = ghc92.hydraJobs.roots;
      hydraJobs.ghc92.plan-nix = ghc92.hydraJobs.plan-nix;

      hydraJobs.ghc96.roots = ghc96.hydraJobs.roots;
      hydraJobs.ghc96.plan-nix = ghc96.hydraJobs.plan-nix;
    })
]
