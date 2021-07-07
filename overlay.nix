{ system, self }:
final: prev:
let
  lib = final.lib;
  # Little convenience function helping us to containing the bash
  # madness: forcing our bash scripts to be shellChecked.
  writeBashChecked = final.writers.makeScriptWriter {
    interpreter = "${final.bash}/bin/bash";
    check = final.writers.writeBash "shellcheck-check" ''
      ${final.shellcheck}/bin/shellcheck "$1"
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

  restic-backup = final.callPackage ./pkgs/backup { };

  plutus = import final.plutus-source { inherit system; };

  devShell = let
    cluster = "plutus-playground";
    domain = final.clusters.${cluster}.proto.config.cluster.domain;
  in prev.mkShell {
    # for bitte-cli
    LOG_LEVEL = "debug";

    BITTE_CLUSTER = cluster;
    AWS_PROFILE = "plutus";
    AWS_DEFAULT_REGION = final.clusters.${cluster}.proto.config.cluster.region;

    VAULT_ADDR = "https://vault.${domain}";
    NOMAD_ADDR = "https://nomad.${domain}";
    CONSUL_HTTP_ADDR = "https://consul.${domain}";

    buildInputs = [
      final.bitte
      self.inputs.bitte.legacyPackages.${system}.scaler-guard
      final.terraform-with-plugins
      prev.sops
      final.vault-bin
      final.openssl
      final.cfssl
      final.nixfmt
      final.awscli
      final.nomad
      final.consul
      final.consul-template
      final.direnv
      final.nixFlakes
      final.jq
      final.fd
    ];
  };

  # Used for caching
  devShellPath = prev.symlinkJoin {
    paths = final.devShell.buildInputs ++ [
      final.nixFlakes
    ];
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

  nixosConfigurations =
    self.inputs.bitte.legacyPackages.${system}.mkNixosConfigurations
    final.clusters;

  clusters = self.inputs.bitte.legacyPackages.${system}.mkClusters {
    root = ./clusters;
    inherit self system;
  };

  inherit (self.inputs.bitte.legacyPackages.${system})
    bitte vault-bin mkNomadJob terraform-with-plugins systemdSandbox nixFlakes
    nomad consul consul-template;

  nomadJobs = let
    jobsDir = ./jobs;
    contents = builtins.readDir jobsDir;
    toImport = name: type: type == "regular" && lib.hasSuffix ".nix" name;
    fileNames = builtins.attrNames (lib.filterAttrs toImport contents);
    imported = lib.forEach fileNames
      (fileName: final.callPackage (jobsDir + "/${fileName}") { });
  in lib.foldl' lib.recursiveUpdate { } imported;

  dockerImages = let
    imageDir = ./docker;
    contents = builtins.readDir imageDir;
    toImport = name: type: type == "regular" && lib.hasSuffix ".nix" name;
    fileNames = builtins.attrNames (lib.filterAttrs toImport contents);
    imported = lib.forEach fileNames
      (fileName: final.callPackages (imageDir + "/${fileName}") { });
    merged = lib.foldl' lib.recursiveUpdate { } imported;
  in lib.flip lib.mapAttrs merged (key: image: {
    inherit image;

    id = "${image.imageName}:${image.imageTag}";

    push = let
      parts = builtins.split "/" image.imageName;
      registry = builtins.elemAt parts 0;
      repo = builtins.elemAt parts 2;
    in final.writeShellScriptBin "push" ''
      set -euo pipefail

      echo -n "Pushing ${image.imageName}:${image.imageTag} ... "

      if curl -s "https://${registry}/v2/${repo}/tags/list" | grep "${image.imageTag}" &> /dev/null; then
        echo "Image already exists in registry"
      else
        docker load -i ${image}
        docker push ${image.imageName}:${image.imageTag}
      fi
    '';

    load = builtins.trace key (final.writeShellScriptBin "load" ''
      set -euo pipefail
      echo "Loading ${image} (${image.imageName}:${image.imageTag}) ..."
      docker load -i ${image}
    '');
  });

  push-docker-images = final.writeShellScriptBin "push-docker-images" ''
    set -euo pipefail
    ${lib.concatStringsSep "\n"
    (lib.mapAttrsToList (key: value: "${value.push}/bin/push")
      final.dockerImages)}
  '';

  load-docker-images = final.writeShellScriptBin "load-docker-images" ''
    set -euo pipefail
    ${lib.concatStringsSep "\n"
    (lib.mapAttrsToList (key: value: "${value.load}/bin/load")
      final.dockerImages)}
  '';

  inherit ((self.inputs.nixpkgs.legacyPackages.${system}).dockerTools)
    buildImage buildLayeredImage shadowSetup;

  mkEnv = lib.mapAttrsToList (key: value: "${key}=${value}");
}
