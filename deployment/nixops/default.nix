let
  plutus = import ../../. {};
  serverTemplate = import ./server.nix;
  prometheusTemplate = import ./prometheus.nix;
  machines = (plutus.pkgs.lib.importJSON ./machines.json);
  overlays = import ./overlays.nix;
  secrets = (plutus.pkgs.lib.importJSON ./secrets.json);
  mkConfig = redirectUrl: name: plutus.pkgs.writeTextFile {
    name = name;
    text = ''
    auth:
      # Maintainers' notes:
      # 1) Github keys and URL in here *must* match the ones set up for this app on
      #    github.
      # 2) If you change the JWT signature, it will break all existing logins.
      #    Don't change it unless that's something you specifically want!
      github-client-id: ${secrets.githubClientId}
      github-client-secret: ${secrets.githubClientSecret}
      jwt-signature: ${secrets.jwtSignature}
      redirect-url: ${redirectUrl}
    '';
  };
  playgroundConfig = mkConfig "https://${machines.environment}.${machines.plutusTld}" "playground.yaml";
  meadowConfig = mkConfig "https://${machines.environment}.${machines.marloweTld}" "marlowe.yaml";
  stdOverlays = [ overlays.journalbeat ];
  options = { inherit stdOverlays machines defaultMachine plutus secrets; };
  defaultMachine = (import ./default-machine.nix) options;
  meadowOptions = options // { serviceConfig = meadowConfig;
                               serviceName = "meadow";
                               server-invoker = plutus.meadow.server-invoker;
                               client = plutus.meadow.client;
                               };
  playgroundOptions = options // { serviceConfig = playgroundConfig;
                                   serviceName = "plutus-playground";
                                   server-invoker = plutus.plutus-playground.server-invoker;
                                   client = plutus.plutus-playground.client;
                                   };
  playgroundA = serverTemplate.mkInstance playgroundOptions machines.playgroundA;
  playgroundB = serverTemplate.mkInstance playgroundOptions machines.playgroundB;
  meadowA = serverTemplate.mkInstance meadowOptions machines.meadowA;
  meadowB = serverTemplate.mkInstance meadowOptions machines.meadowB;
  nixops = prometheusTemplate.mkInstance options {dns = "nixops.internal.${machines.environment}.${machines.plutusTld}";
                                                  ip = "127.0.0.1";
                                                  name = "nixops"; };
in
  { inherit playgroundA playgroundB meadowA meadowB nixops; }
