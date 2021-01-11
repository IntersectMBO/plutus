{ pkgs, nix-gitignore, set-git-rev, haskell, webCommon, buildPursPackage, buildNodeModules }:
let
  server-invoker = set-git-rev haskell.packages.plutus-scb.components.exes.plutus-scb;

  generated-purescript = pkgs.runCommand "plutus-scb-purescript" { } ''
    mkdir $out
    ln -s ${haskell.packages.plutus-scb.src}/plutus-scb.yaml.sample plutus-scb.yaml
    ${server-invoker}/bin/plutus-scb psgenerator $out
  '';

  nodeModules = buildNodeModules {
    projectDir = nix-gitignore.gitignoreSource [ "/*.nix" "/*.md" ] ./.;
    packageJson = ./package.json;
    packageLockJson = ./package-lock.json;
  };

  client =
    buildPursPackage {
      inherit webCommon nodeModules;
      src = ./.;
      name = "plutus-scb-client";
      # ideally we would just use `npm run test` but
      # this executes `spago` which *always* attempts to download
      # remote files (which obviously fails in sandboxed builds)
      checkPhase = ''
        node -e 'require("./output/Test.Main").main()'
      '';
      psSrc = generated-purescript;
      packages = pkgs.callPackage ./packages.nix { };
      spagoPackages = pkgs.callPackage ./spago-packages.nix { };
    };

  demo-scripts = (dbPath: pkgs.callPackage ./pab-demo-scripts.nix { inherit pkgs dbPath client; scb-exes = haskell.packages.plutus-scb.components.exes; });

in
{
  inherit client demo-scripts server-invoker generated-purescript;
}
