{ pkgs, gitignore-nix, set-git-rev, haskell, webCommon, webCommonPlutus, buildPursPackage, buildNodeModules }:
let
  server-invoker = set-git-rev haskell.packages.plutus-pab.components.exes.plutus-pab;

  generated-purescript = pkgs.runCommand "plutus-pab-purescript" { } ''
    mkdir $out
    ln -s ${haskell.packages.plutus-pab.src}/plutus-pab.yaml.sample plutus-pab.yaml
    ${server-invoker}/bin/plutus-pab psgenerator $out
  '';

  # For dev usage
  generate-purescript = pkgs.writeShellScriptBin "plutus-pab-generate-purs" ''
    rm -rf ./generated
    # There might be local modifications so only copy when missing
    ! test -f ./plutus-pab.yaml && cp ../plutus-pab/plutus-pab.yaml.sample plutus-pab.yaml
    $(nix-build ../default.nix --quiet --no-build-output -A plutus-pab.server-invoker)/bin/plutus-pab psgenerator generated
  '';

  # For dev usage
  start-backend = pkgs.writeShellScriptBin "plutus-pab-server" ''
    export FRONTEND_URL=https://localhost:8009
    export WEBGHC_URL=http://localhost:8080
    rm -rf ./generated
    # There might be local modifications so only copy when missing
    ! test -f ./plutus-pab.yaml && cp ../plutus-pab/plutus-pab.yaml.sample plutus-pab.yaml
    $(nix-build ../default.nix --quiet --no-build-output -A plutus-pab.server-invoker)/bin/plutus-pab webserver
  '';

  cleanSrc = gitignore-nix.gitignoreSource ./.;

  nodeModules = buildNodeModules {
    projectDir = cleanSrc;
    packageJson = ./package.json;
    packageLockJson = ./package-lock.json;
  };

  client =
    buildPursPackage {
      inherit pkgs nodeModules;
      src = cleanSrc;
      name = "plutus-pab-client";
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

  demo-scripts = (dbPath: pkgs.callPackage ./pab-demo-scripts.nix { inherit pkgs dbPath client; pab-exes = haskell.packages.plutus-pab.components.exes; });

in
{
  inherit client demo-scripts server-invoker generated-purescript generate-purescript start-backend;
}
