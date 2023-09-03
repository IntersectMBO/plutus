{ repoRoot, pkgs, lib, system, config, ... }:

let 

  ghc8107 = config.cabalProjects.ghc8107.outputs;
  ghc927 = config.cabalProjects.ghc927.outputs;
  ghc962 = config.cabalProjects.ghc962.outputs;

in 

[
  {
    cabalProjects.ghc8107.project = repoRoot.nix.make-project "ghc8107";
    cabalProjects.ghc8107.shell = repoRoot.nix.make-shell "ghc8107";

    cabalProjects.ghc962.project = repoRoot.nix.make-project "ghc962";
    cabalProjects.ghc962.shell = repoRoot.nix.make-shell "ghc962";

    cabalProjects.ghc927.project = repoRoot.nix.make-project "ghc927";
    cabalProjects.ghc927.shell = repoRoot.nix.make-shell "ghc927";
    cabalProjects.ghc927.read-the-docs.siteFolder = ../doc/read-the-docs-site;
    cabalProjects.ghc927.combined-haddock = repoRoot.nix.combined-haddock;
  }
  {
    packages = ghc927.packages;
    checks = ghc927.checks;

    devShells.default = ghc927.devShell;
    devShells.profiled = ghc927.project.profiled.devShell;
    devShells.ghc8107 = ghc8107.devShell;
    devShells.ghc927 = ghc927.devShell;
    devShells.ghc927 = ghc962.devShell;
  }
  {
    latex-documents = repoRoot.nix.latex-documents;
    packages.plutus-metatheory-site = repoRoot.nix.plutus-metatheory-site;
    packages.read-the-docs-site = ghc927.read-the-docs-site;
    packages.pre-commit-check = ghc927.pre-commit-check;
  }
  (lib.mkIf (system == "x86_64-linux") 
  {
    hydraJobs.latex-documents = repoRoot.nix.latex-documents;
    hydraJobs.packages.read-the-docs-site = ghc927.read-the-docs-site;

    hydraJobs.mingwW64.ghc8107 = ghc8107.project.mingwW64.hydraJobs;
    hydraJobs.mingwW64.ghc927 = ghc927.project.mingwW64.hydraJobs;
    hydraJobs.mingwW64.ghc962 = ghc962.project.mingwW64.hydraJobs;
  })
  (lib.mkIf (system == "x86_64-linux" || system == "x86_64-darwin") 
  {
    hydraJobs.packages.plutus-metatheory-site = repoRoot.nix.plutus-metatheory-site;
    hydraJobs.packages.pre-commit-check = ghc927.pre-commit-check;

    hydraJobs.ghc8107 = ghc8107.hydraJobs; 
    hydraJobs.ghc927 = ghc927.hydraJobs; 
    hydraJobs.ghc962 = ghc962.hydraJobs; 
  })
  (lib.mkIf (sytem == "aarch64-darwin") 
  {
    # Plausibly if things build on x86 darwin then they'll build on aarch darwin.
    # Se we only build roots and devshells on aarch to avoid overloading the builders.
    # Note: We can't build the 9.6 shell on aarch64-darwin
    # because of https://github.com/well-typed/cborg/issues/311
    hydraJobs.ghc8107.devShell = ghc8107.hydraJobs.devShell; 
    hydraJobs.ghc927.devShell = ghc927.hydraJobs.devShell; 

    hydraJobs.ghc8107.roots = ghc8107.hydraJobs.roots;
    hydraJobs.ghc8107.plan-nix = ghc8107.hydraJobs.plan-nix;

    hydraJobs.ghc927.roots = ghc927.hydraJobs.roots;
    hydraJobs.ghc927.plan-nix = ghc927.hydraJobs.plan-nix;

    hydraJobs.ghc962.roots = ghc962.hydraJobs.roots;
    hydraJobs.ghc962.plan-nix = ghc962.hydraJobs.plan-nix;
  })
]


