{ system, self }:
let extraJobArgs = { };
in final: prev:
let lib = final.lib;
in {

  nomadJobs = let
    jobsDir = ./jobs;
    contents = builtins.readDir jobsDir;
    toImport = name: type: type == "regular" && lib.hasSuffix ".nix" name;
    fileNames = builtins.attrNames (lib.filterAttrs toImport contents);
    imported = lib.forEach fileNames
      (fileName: final.callPackage (jobsDir + "/${fileName}") extraJobArgs);
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

    push = final.writeShellScriptBin "push" ''
      set -euo pipefail
      echo "Pushing ${image} (${image.imageName}:${image.imageTag}) ..."
      docker load -i ${image}
      docker push ${image.imageName}:${image.imageTag}
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
    buildLayeredImage;

  mkEnv = lib.mapAttrsToList (key: value: "${key}=${value}");

  devShell = let
    cluster = "plutus-testnet";
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
    NIX_USER_CONF_FILES = ./nix.conf;

    buildInputs = [
      final.bitte
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
      final.python38Packages.pyhcl
      final.direnv
      final.nixFlakes
      final.jq
    ];
  };

  # Used for caching
  devShellPath = prev.symlinkJoin {
    paths = final.devShell.buildInputs;
    name = "devShell";
  };

  nixosConfigurations =
    self.inputs.bitte.legacyPackages.${system}.mkNixosConfigurations
    final.clusters;

  clusters = self.inputs.bitte.legacyPackages.${system}.mkClusters {
    root = ./clusters;
    inherit self system;
  };

  inherit (self.inputs.bitte.legacyPackages.${system})
    vault-bin mkNomadJob terraform-with-plugins systemdSandbox nixFlakes nomad
    consul consul-template systemd-runner grpcdump;

  # inject vault-bin into bitte wrapper
  bitte = let
    bitte-nixpkgs = import self.inputs.nixpkgs {
      inherit system;
      overlays = [
        (final: prev: {
          vault-bin = self.inputs.bitte.legacyPackages.${system}.vault-bin;
        })
        self.inputs.bitte-cli.overlay.${system}
      ];
    };
  in bitte-nixpkgs.bitte;
}
