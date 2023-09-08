{ repoRoot, inputs, pkgs, lib, system, ... }:

let
  cabalProject = repoRoot.nix.cabal-project;

  ghc8107 = cabalProject.projectVariants.ghc8107;
  ghc927 = cabalProject.projectVariants.ghc927;
  ghc927-profiled = cabalProject.projectVariants.ghc927-profiled;
  ghc962 = cabalProject.projectVariants.ghc962;

in

[
  {
    inherit cabalProject;
  }
  {
    devShells.default = ghc927.iogx.devShell;
    devShells.profiled = ghc927-profiled.iogx.devShell;
    devShells.ghc927 = ghc927.iogx.devShell;
    devShells.ghc8107 = ghc8107.iogx.devShell;
    devShells.ghc962 = ghc962.iogx.devShell;
  }
  {
    latex-documents = repoRoot.nix.latex-documents;

    packages.plutus-metatheory-site = repoRoot.nix.plutus-metatheory-site;
    packages.pre-commit-check = ghc927.pre-commit-check;
    packages.read-the-docs-site = ghc927.read-the-docs-site;
  }
  {
    hydraJobs.required = lib.iogx.mkHydraRequiredJob;
  }
  (lib.optionalAttrs (system == "x86_64-linux" || system == "x86_64-darwin")
    {
      hydraJobs.plutus-metatheory-site = repoRoot.nix.plutus-metatheory-site;
      hydraJobs.pre-commit-check = ghc927.iogx.pre-commit-check;

      hydraJobs.ghc8107 = ghc8107.iogx.hydraJobs;
      hydraJobs.ghc927 = ghc927.iogx.hydraJobs;
      hydraJobs.ghc962 = ghc962.iogx.hydraJobs;
    })
  (lib.optionalAttrs (system == "x86_64-linux")
    {
      hydraJobs.latex-documents = inputs.self.latex-documents;
      hydraJobs.read-the-docs-site = inputs.self.packages.read-the-docs-site;

      hydraJobs.mingwW64.ghc8107 = ghc8107.projectCross.mingwW64.iogx.hydraJobs;
      hydraJobs.mingwW64.ghc927 = ghc927.projectCross.mingwW64.iogx.hydraJobs;
      hydraJobs.mingwW64.ghc962 = ghc962.projectCross.mingwW64.iogx.hydraJobs;
    })
  (lib.optionalAttrs (system == "aarch64-darwin")
    {
      # Plausibly if things build on x86 darwin then they'll build on aarch darwin.
      # Se we only build roots and devshells on aarch to avoid overloading the builders.
      # Note: We can't build the 9.6 shell on aarch64-darwin
      # because of https://github.com/well-typed/cborg/issues/311
      hydraJobs.ghc8107.devShell = ghc8107.iogx.devShell;
      hydraJobs.ghc927.devShell = ghc927.iogx.devShell;

      hydraJobs.ghc8107.roots = ghc8107.iogx.hydraJobs.roots;
      hydraJobs.ghc8107.plan-nix = ghc8107.iogx.hydraJobs.plan-nix;

      hydraJobs.ghc927.roots = ghc927.iogx.hydraJobs.roots;
      hydraJobs.ghc927.plan-nix = ghc927.iogx.hydraJobs.plan-nix;

      hydraJobs.ghc962.roots = ghc962.iogx.hydraJobs.roots;
      hydraJobs.ghc962.plan-nix = ghc962.iogx.hydraJobs.plan-nix;
    })
]


