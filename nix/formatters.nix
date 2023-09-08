# This file is part of the IOGX template and is documented at the link below:
# https://www.github.com/input-output-hk/iogx#38-nixformattersnix

{
  stylish-haskell.enable = true;
  cabal-fmt.enable = true;
  shellcheck.enable = true;
  editorconfig-checker.enable = true;
  nixpkgs-fmt.enable = true;
  png-optimization.enable = true;

  # TODO
  # open a new PR
  # set this to true
  # run 'pre-commit run hlint --all-files'
  # fix everything up
  # push & merge
  # remove this comment
  hlint.enable = false;
}
