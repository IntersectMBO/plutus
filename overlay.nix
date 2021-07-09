inputs: final: prev:
let
  lib = final.lib;
  # Little convenience function helping us to containing the bash
  # madness: forcing our bash scripts to be shellChecked.
  writeBashChecked = final.writers.makeScriptWriter {
    interpreter = "${final.bash}/bin/bash";
    check = final.writers.writeBash "shellcheck-check" ''
      ${final.shellcheck}/bin/shellcheck -x "$1"
    '';
  };
  writeBashBinChecked = name: writeBashChecked "/bin/${name}";
in {
  inherit writeBashChecked writeBashBinChecked;
  plutus-source = builtins.fetchGit {
    url = "https://github.com/input-output-hk/plutus";
    rev = "4fc1d4ab5396f206319387e0283d597ea390f6b8";
    ref = "master";
  };

  # Any:
  # - run of this command with a parameter different than the testnet (currently 10)
  # - change in the genesis file here
  # Requires an update on the mantis repository and viceversa
  generate-mantis-keys = final.writeBashBinChecked "generate-mantis-keys" ''
    export PATH="${
      lib.makeBinPath (with final; [
        coreutils
        curl
        gawk
        gnused
        gnused
        jq
        mantis
        netcat
        vault-bin
        which
        shellcheck
        tree
      ])
    }"

    . ${./pkgs/generate-mantis-keys.sh}
  '';

  plutus = import final.plutus-source { inherit (final) system; };
  checkFmt = final.writeShellScriptBin "check_fmt.sh" ''
    export PATH="$PATH:${lib.makeBinPath (with final; [ git nixfmt gnugrep ])}"
    . ${./pkgs/check_fmt.sh}
  '';

  devShell = let
    cluster = "plutus-playground";
    domain = final.clusters.${cluster}.proto.config.cluster.domain;
  in prev.mkShell {
    # for bitte-cli
    LOG_LEVEL = "debug";

    BITTE_CLUSTER = cluster;
    AWS_PROFILE = "plutus";
    AWS_DEFAULT_REGION = final.clusters.${cluster}.proto.config.cluster.region;
    NOMAD_NAMESPACE = "plutus-playground";

    VAULT_ADDR = "https://vault.${domain}";
    NOMAD_ADDR = "https://nomad.${domain}";
    CONSUL_HTTP_ADDR = "https://consul.${domain}";

    buildInputs = with final; [
      bitte
      scaler-guard
      terraform-with-plugins
      sops
      vault-bin
      openssl
      cfssl
      ripgrep
      nixfmt
      awscli
      nomad
      consul
      consul-template
      direnv
      jq
      fd
      cue
    ];
  };

  # Used for caching
  devShellPath = prev.symlinkJoin {
    paths = final.devShell.buildInputs;
    name = "devShell";
  };

  debugUtils = with final; [
    bashInteractive
    coreutils
    curl
    dnsutils
    fd
    gawk
    gnugrep
    iproute
    jq
    lsof
    netcat
    nettools
    procps
    tree
  ];


  restic-backup = final.callPackage ./pkgs/backup { };
}
