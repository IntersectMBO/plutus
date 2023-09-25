{ repoRoot, inputs, pkgs, lib, system, ... }:

let
  cabalProject = repoRoot.nix.cabal-project;

  ghc810 = cabalProject.projectVariants.ghc810;
  ghc92 = cabalProject.projectVariants.ghc92;
  ghc92-profiled = cabalProject.projectVariants.ghc92-profiled;
  ghc96 = cabalProject.projectVariants.ghc96;

in

[
  {
    inherit cabalProject;
  }
  {
    devShells.default = cabalProject.iogx.devShell;
    devShells.profiled = ghc92-profiled.iogx.devShell;
    devShells.ghc92 = ghc92.iogx.devShell;
    devShells.ghc810 = ghc810.iogx.devShell;
    devShells.ghc96 = ghc96.iogx.devShell;
  }
  {
    latex-documents = repoRoot.nix.latex-documents;

    packages.plutus-metatheory-site = repoRoot.nix.plutus-metatheory-site;
    packages.pre-commit-check = ghc92.pre-commit-check;
    packages.read-the-docs-site = ghc92.read-the-docs-site;
  }
  {
    hydraJobs.required = lib.iogx.mkHydraRequiredJob;
  }
  (lib.optionalAttrs (system == "x86_64-linux" || system == "x86_64-darwin")
    {
      hydraJobs.plutus-metatheory-site = repoRoot.nix.plutus-metatheory-site;
      hydraJobs.pre-commit-check = ghc92.iogx.pre-commit-check;

      hydraJobs.ghc810 = ghc810.iogx.hydraJobs;
      hydraJobs.ghc92 = ghc92.iogx.hydraJobs;
      hydraJobs.ghc96 = ghc96.iogx.hydraJobs;
    })
  (lib.optionalAttrs (system == "x86_64-linux")
    {
      hydraJobs.latex-documents = inputs.self.latex-documents;
      hydraJobs.read-the-docs-site = inputs.self.packages.read-the-docs-site;

      hydraJobs.mingwW64.ghc810 = ghc810.projectCross.mingwW64.iogx.hydraJobs;
      hydraJobs.mingwW64.ghc92 = ghc92.projectCross.mingwW64.iogx.hydraJobs;
      hydraJobs.mingwW64.ghc96 = ghc96.projectCross.mingwW64.iogx.hydraJobs;
    })
  (lib.optionalAttrs (system == "aarch64-darwin")
    {
      # Plausibly if things build on x86 darwin then they'll build on aarch darwin.
      # Se we only build roots and devshells on aarch to avoid overloading the builders.
      # Note: We can't build the 9.6 shell on aarch64-darwin
      # because of https://github.com/well-typed/cborg/issues/311
      hydraJobs.ghc810.devShell = ghc810.iogx.devShell;
      hydraJobs.ghc92.devShell = ghc92.iogx.devShell;

      hydraJobs.ghc810.roots = ghc810.iogx.hydraJobs.roots;
      hydraJobs.ghc810.plan-nix = ghc810.iogx.hydraJobs.plan-nix;

      hydraJobs.ghc92.roots = ghc92.iogx.hydraJobs.roots;
      hydraJobs.ghc92.plan-nix = ghc92.iogx.hydraJobs.plan-nix;

      hydraJobs.ghc96.roots = ghc96.iogx.hydraJobs.roots;
      hydraJobs.ghc96.plan-nix = ghc96.iogx.hydraJobs.plan-nix;
    })
]


