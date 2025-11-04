{ pkgs }:

# R wrapper with required packages for benchmarking and analysis.
# Add more R packages here as needed.
# Used in: `nix/project.nix` (as build-tools) and `nix/shell.nix` common tools.
pkgs.rWrapper.override {
  packages = [
    pkgs.rPackages.tidyverse
    pkgs.rPackages.dplyr
    pkgs.rPackages.stringr
    pkgs.rPackages.MASS
    pkgs.rPackages.plotly
    pkgs.rPackages.shiny
    pkgs.rPackages.shinyjs
    pkgs.rPackages.purrr
  ];
}
