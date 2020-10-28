let
  plutus = import ../../. { };
  prometheusTemplate = import ./prometheus.nix;
  webghc = import ./webghc.nix;
  machines = (plutus.pkgs.lib.importJSON ./machines.json);
  overlays = import ./overlays.nix;
  secrets = (plutus.pkgs.lib.importJSON ./secrets.json);
  enableGithubHooks = plutus.pkgs.lib.hasAttr "githubWebhookKey" secrets;
  deploymentConfigDir = plutus.pkgs.copyPathToStore ../nixops;
  deploymentServer = plutus.haskell.packages.deployment-server.components.exes.deployment-server-exe;
  stdOverlays = [ overlays.journalbeat ];
  nixpkgsLocation = https://github.com/NixOS/nixpkgs/archive/5272327b81ed355bbed5659b8d303cf2979b6953.tar.gz;
  nixosLocation = "/root/.nix-defexpr/channels/nixos";
  slackChannel = "plutus-notifications";
  nixopsStateFile = "/root/.nixops/deployments.nixops";
  deploymentName = "playgrounds";
  options = { inherit stdOverlays machines defaultMachine plutus secrets nixpkgsLocation nixosLocation slackChannel nixopsStateFile deploymentName; };
  defaultMachine = (import ./default-machine.nix) options;
  webGhcA = webghc.mkInstance (options // { web-ghc = plutus.web-ghc; }) machines.webGhcA;
  webGhcB = webghc.mkInstance (options // { web-ghc = plutus.web-ghc; }) machines.webGhcA;
  nixops = prometheusTemplate.mkInstance
    (options // { configDir = deploymentConfigDir; inherit deploymentServer enableGithubHooks; })
    {
      dns = "nixops.internal.${machines.environment}.${machines.plutusTld}";
      ip = "127.0.0.1";
      name = "nixops";
    };
in
{ inherit nixops webGhcA webGhcB; }
