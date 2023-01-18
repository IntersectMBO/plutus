{ inputs, cell }:

let
  inherit (cell.library) pkgs;
in

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
