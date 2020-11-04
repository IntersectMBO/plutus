{ dockerTools
, binutils-unwrapped
, coreutils
, bash
, git
, cabal-install
, writeTextFile
, plutus-playground
, marlowe-playground
, haskell
}:

let defaultPlaygroundConfig = writeTextFile {
  name = "playground.yaml";
  destination = "/etc/playground.yaml";
  text = ''
    auth:
      github-client-id: ""
      github-client-secret: ""
      jwt-signature: ""
      redirect-url: "localhost:8080"
  '';
};
in
{
  plutusPlaygroundImage = with plutus-playground; dockerTools.buildLayeredImage {
    name = "plutus-playgrounds";
    contents = [ client server-invoker defaultPlaygroundConfig ];
    config = {
      Cmd = [ "${server-invoker}/bin/plutus-playground" "--config" "${defaultPlaygroundConfig}/etc/playground.yaml" "webserver" "-b" "0.0.0.0" "-p" "8080" "${client}" ];
    };
  };
  marlowePlaygroundImage = with marlowe-playground; dockerTools.buildLayeredImage {
    name = "marlowe-playground";
    contents = [ client server-invoker defaultPlaygroundConfig ];
    config = {
      Cmd = [ "${server-invoker}/bin/marlowe-playground" "--config" "${defaultPlaygroundConfig}/etc/playground.yaml" "webserver" "-b" "0.0.0.0" "-p" "8080" "${client}" ];
    };
  };

  development = dockerTools.buildLayeredImage {
    name = "plutus-development";
    contents =
      let runtimeGhc =
        haskell.packages.ghcWithPackages (ps: [
          ps.plutus-core
          ps.plutus-ledger
          ps.plutus-tx
          ps.plutus-tx-plugin
          ps.plutus-use-cases
          ps.plutus-contract
        ]);
      in
      [
        runtimeGhc
        binutils-unwrapped
        coreutils
        bash
        git # needed by cabal-install
        cabal-install
      ];
    config = {
      Cmd = [ "bash" ];
    };
  };
}
