{ pkgs, gitignore-nix, haskell, webCommon, webCommonPlutus, buildPursPackage, buildNodeModules, filterNpm }:
let
  server-invoker = haskell.packages.plutus-pab.components.exes.plutus-pab;

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
  migrate = pkgs.writeShellScriptBin "plutus-pab-migrate" ''
    # There might be local modifications so only copy when missing
    ! test -f ./plutus-pab.yaml && cp ../plutus-pab/plutus-pab.yaml.sample plutus-pab.yaml
    $(nix-build ../default.nix --quiet --no-build-output -A plutus-pab.server-invoker)/bin/plutus-pab migrate
  '';

  # For dev usage
  start-backend = pkgs.writeShellScriptBin "plutus-pab-server" ''
    export FRONTEND_URL=https://localhost:8009
    export WEBGHC_URL=https://localhost:8888
    # There might be local modifications so only copy when missing
    ! test -f ./plutus-pab.yaml && cp ../plutus-pab/plutus-pab.yaml.sample plutus-pab.yaml
    $(nix-build ../default.nix --quiet --no-build-output -A plutus-pab.server-invoker)/bin/plutus-pab webserver
  '';

  # For dev usage
  start-all-servers = pkgs.writeShellScriptBin "plutus-pab-all-servers" ''
    export FRONTEND_URL=https://localhost:8009
    export WEBGHC_URL=https://localhost:8888
    # There might be local modifications so only copy when missing
    ! test -f ./plutus-pab.yaml && cp ../plutus-pab/plutus-pab.yaml.sample plutus-pab.yaml
    $(nix-build ../default.nix --quiet --no-build-output -A plutus-pab.server-invoker)/bin/plutus-pab all-servers
  '';

  cleanSrc = gitignore-nix.gitignoreSource ./.;

  nodeModules = buildNodeModules {
    projectDir = filterNpm cleanSrc;
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

  pab-exes = haskell.packages.plutus-pab.components.exes;

  demo-scripts = pkgs.callPackage ./pab-demo-scripts.nix { inherit client pab-exes; };

  mkConf = pkgs.callPackage ./config.nix { };

in
{
  inherit client demo-scripts server-invoker generated-purescript generate-purescript migrate start-backend start-all-servers mkConf pab-exes;
}
