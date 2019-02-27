let
  plutus = import ../../. {};
  playgroundMachine = import ./playground.nix;
  meadowMachine = import ./meadow.nix;
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
  playgroundConfig = mkConfig "https://david.plutus.iohkdev.io" "playground.yaml";
  meadowConfig = mkConfig "https://david.marlowe.iohkdev.io" "marlowe.yaml";
  stdOverlays = [ overlays.journalbeat ];
  options = { inherit stdOverlays machines defaultMachine plutus playgroundConfig meadowConfig; datadogKey = secrets.datadogKey; };
  defaultMachine = (import ./default-machine.nix) options;
  playgroundA = playgroundMachine.mkInstance options machines.playgroundA;
  playgroundB = playgroundMachine.mkInstance options machines.playgroundB;
  meadowA = meadowMachine.mkInstance options machines.meadowA;
  meadowB = meadowMachine.mkInstance options machines.meadowB;
in
  { inherit playgroundA playgroundB meadowA meadowB; }
