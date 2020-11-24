{ pkgs, set-git-rev, haskell, webCommon, buildPursPackage }:
let
  server-invoker = set-git-rev haskell.packages.plutus-scb.components.exes.plutus-scb;

  generated-purescript = pkgs.runCommand "plutus-scb-purescript" { } ''
    mkdir $out
    ln -s ${haskell.packages.plutus-scb.src}/plutus-scb.yaml.sample plutus-scb.yaml
    ${server-invoker}/bin/plutus-scb psgenerator $out
  '';
  client =
    buildPursPackage {
      inherit webCommon;
      src = ./.;
      name = "plutus-scb-client";
      psSrc = generated-purescript;
      packages = pkgs.callPackage ./packages.nix { };
      spagoPackages = pkgs.callPackage ./spago-packages.nix { };
    };

  demo-scripts = (dbPath: pkgs.callPackage ./pab-demo-scripts.nix { inherit pkgs dbPath client; scb-exes = haskell.packages.plutus-scb.components.exes; });

in
{
  inherit client demo-scripts server-invoker generated-purescript;
}
