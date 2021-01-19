{ pkgs, nix-gitignore, set-git-rev, haskell, webCommon, webCommonPlutus, buildPursPackage, buildNodeModules }:
let
  server-invoker = set-git-rev haskell.packages.plutus-scb.components.exes.plutus-scb;

  generated-purescript = pkgs.runCommand "plutus-scb-purescript" { } ''
    mkdir $out
    ln -s ${haskell.packages.plutus-scb.src}/plutus-scb.yaml.sample plutus-scb.yaml
    ${server-invoker}/bin/plutus-scb psgenerator $out
  '';

  # For dev usage
  generate-purescript = pkgs.writeShellScript "plutus-scb-generate-purescript" ''
    rm -rf ./generated
    ${server-invoker}/bin/plutus-scb psgenerator generated
  '';

  nodeModules = buildNodeModules {
    projectDir = nix-gitignore.gitignoreSource [ "/*.nix" "/*.md" ] ./.;
    packageJson = ./package.json;
    packageLockJson = ./package-lock.json;
  };

  client =
    buildPursPackage {
      inherit pkgs nodeModules;
      src = ./.;
      name = "plutus-scb-client";
      extraSrcs = {
        web-common = webCommon;
        web-common-plutus = webCommonPlutus;
        generated = generated-purescript;
      };
      # ideally we would just use `npm run test` but
      # this executes `spago` which *always* attempts to download
      # remote files (which obviously fails in sandboxed builds)
      checkPhase = ''
        node -e 'require("./output/Test.Main").main()'
      '';
      packages = pkgs.callPackage ./packages.nix { };
      spagoPackages = pkgs.callPackage ./spago-packages.nix { };
    };

  demo-scripts = (dbPath: pkgs.callPackage ./pab-demo-scripts.nix { inherit pkgs dbPath client; scb-exes = haskell.packages.plutus-scb.components.exes; });

in
{
  inherit client demo-scripts server-invoker generated-purescript generate-purescript;
}
