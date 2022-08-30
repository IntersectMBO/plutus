{ inputs, cell }@organelle:
{
  sphinx-markdown-tables = import ./sphinx-markdown-tables.nix organelle;

  sphinxemoji = import ./sphinxemoji.nix organelle;

  inherit (import ./sphinxcontrib-haddock.nix organelle)

    sphinxcontrib-domaintools 

    sphinxcontrib-haddock
    
    sphobjinv; 

  git-work-in-progress = import ./git-work-in-progress.nix organelle;

  repo-root = import ./repo-root.nix organelle;

  # TODO(std) uncomment once we've done haskell.nix
  #agda-with-stdlib = import ./agda-with-stdlib.nix organelle;

  # TODO(std) make this part of CI
  check-the-flake = import ./check-the-flake.nix organelle;
}