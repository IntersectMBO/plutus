{ pkgs, set-git-rev, haskell, easyPS, nodejs-headers, webCommon }:

let
  server-invoker = set-git-rev haskell.packages.plutus-scb.components.exes.plutus-scb;

  generated-purescript = pkgs.runCommand "plutus-scb-purescript" { } ''
    mkdir $out
    ln -s ${haskell.packages.plutus-scb.src}/plutus-scb.yaml.sample plutus-scb.yaml
    ${server-invoker}/bin/plutus-scb psgenerator $out
  '';
  client =
    pkgs.callPackage ../nix/lib/purescript.nix rec {
      inherit nodejs-headers;
      inherit easyPS webCommon;
      psSrc = generated-purescript;
      src = ./.;
      packageJSON = ./package.json;
      yarnLock = ./yarn.lock;
      yarnNix = ./yarn.nix;
      additionalPurescriptSources = [ "../web-common/**/*.purs" ];
      packages = pkgs.callPackage ./packages.nix { };
      spagoPackages = pkgs.callPackage ./spago-packages.nix { };
      name = (pkgs.lib.importJSON packageJSON).name;
      checkPhase = ''node -e 'require("./output/Test.Main").main()' '';
    };

  demo-scripts = (dbPath: pkgs.callPackage ./pab-demo-scripts.nix { inherit pkgs dbPath client; scb-exes = haskell.packages.plutus-scb.components.exes; });

in
{
  inherit client demo-scripts;
}
