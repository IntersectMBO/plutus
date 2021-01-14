{ pkgs, nix-gitignore, set-git-rev, haskell, webCommon, buildPursPackage, buildNodeModules }:
let
  playground-exe = set-git-rev haskell.packages.marlowe-playground-server.components.exes.marlowe-playground-server;

  server-invoker =
    let
      # the playground uses ghc at runtime so it needs one packaged up with the dependencies it needs in one place
      runtimeGhc = haskell.project.ghcWithPackages (ps: [
        ps.marlowe
        ps.marlowe-playground-server
      ]);
    in
    pkgs.runCommand "marlowe-server-invoker" { buildInputs = [ pkgs.makeWrapper ]; } ''
      # We need to provide the ghc interpreter with the location of the ghc lib dir and the package db
      mkdir -p $out/bin
      ln -s ${playground-exe}/bin/marlowe-playground-server $out/bin/marlowe-playground
      wrapProgram $out/bin/marlowe-playground \
        --set GHC_LIB_DIR "${runtimeGhc}/lib/ghc-${runtimeGhc.version}" \
        --set GHC_BIN_DIR "${runtimeGhc}/bin" \
        --set GHC_PACKAGE_PATH "${runtimeGhc}/lib/ghc-${runtimeGhc.version}/package.conf.d" \
        --set GHC_RTS "-M2G"
    '';

  generated-purescript = pkgs.runCommand "marlowe-playground-purescript" { } ''
    mkdir $out
    ${playground-exe}/bin/marlowe-playground-server psgenerator $out
  '';

  nodeModules = buildNodeModules {
    projectDir = nix-gitignore.gitignoreSource [ "/*.nix" "/*.md" ] ./.;
    packageJson = ./package.json;
    packageLockJson = ./package-lock.json;
    githubSourceHashMap = {
      shmish111.nearley-webpack-loader."939360f9d1bafa9019b6ff8739495c6c9101c4a1" = "1brx669dgsryakf7my00m25xdv7a02snbwzhzgc9ylmys4p8c10x";
      znerol.libxmljs."0517e063347ea2532c9fdf38dc47878c628bf0ae" = "0g3kgwnqfr6v2xp1i7dfbm4z45inz1019ln06lfxl9mwxlc31wfg";
    };
  };

  client = buildPursPackage {
    inherit webCommon nodeModules;
    src = ./.;
    checkPhase = "npm run test";
    name = "marlowe-playground-client";
    psSrc = generated-purescript;
    packages = pkgs.callPackage ./packages.nix { };
    spagoPackages = pkgs.callPackage ./spago-packages.nix { };
  };
in
{
  inherit client server-invoker generated-purescript;
}
