{ pkgs ? (import ./.. { }).pkgs }:
with pkgs;
let
  # Creates a deployment shell environment
  mkDeploymentShell = pkgs.callPackage ./deployment-shell.nix { };


  /* We store developers public gpg keys in this project so this is a little
     script that imports all the relevant keys.
  */
  importKeys =
    let
      nameToFile = name: ./. + "/keys/${name}";
      keyFiles = lib.mapAttrsToList (name: value: nameToFile value.name) keys;
      lines = map (k: "gpg --import ${k}") keyFiles;
    in
    writeShellScriptBin "import-gpg-keys" (lib.concatStringsSep "\n" lines);

  /* This will change an environment's pass entry to work with specific people's keys
     i.e. If you want to enable a new developer to deploy to a specific environment you
     need to add them to the list of keys for the environment and then re-encrypt with
     this script.
  */
  initPass = env: keys:
    let
      ids = map (k: k.id) keys;
    in
    writeShellScriptBin "init-keys-${env}" ''
      pass init -p ${env} ${lib.concatStringsSep " " ids}
    '';

  /* The set of all gpg keys that can be used by pass
     To add a new user, put their key in ./deployment/keys and add the key filename and id here.
     You can cheat the id by putting an empty value and then running `$(nix-build -A deployment.importKeys)`
     and then finding the key id with `gpg --list-keys` and updating this set.
  */
  keys = {
    kris = { name = "kris.jenkins.gpg"; id = "7EE9B7DE0F3CA25DB5B93D88A1ABC88D19C8136C"; };
    pablo = { name = "pablo.lamela.gpg"; id = "52AB1370A5BB41307470F9B05BA76ACFF04A2ACD"; };
    hernan = { name = "hernan.rajchert.gpg"; id = "AFF6767D33EFF77D519EE6B8C7BBC002683C8DCB"; };
    tobias = { name = "tobias.pflug.gpg"; id = "46681E3759BA8680B3180AA0EBA3115F56AA2315"; };
    amyas = { name = "amyas.merivale.gpg"; id = "8504C0C97F2164419433AAF63F91FB4358BD1137"; };
  };

  envs = {
    kris = { region = "eu-west-1"; keys = [ keys.kris ]; };
    alpha = { region = "eu-west-2"; keys = with keys; [ kris pablo hernan tobias amyas ]; };
    pablo = { region = "eu-west-3"; keys = [ keys.pablo ]; };
    playground = { region = "us-west-1"; keys = with keys; [ kris pablo hernan tobias amyas ]; };
    testing = { region = "eu-west-3"; keys = with keys; [ kris pablo hernan tobias amyas ]; };
    hernan = { region = "us-west-2"; keys = [ keys.hernan ]; };
    tobias = { region = "eu-west-1"; keys = [ keys.tobias ]; };
    amyas = { region = "eu-west-2"; keys = [ keys.amyas ]; };

    # this is anything that is defined in $PLUTUS_HOME/infrastructure such as the grafana instance
    #TODO: global = { initPass = (initPass "global" [ keys.kris keys.pablo keys.hernan ]); };
  };


in
builtins.mapAttrs
  (env: cfg: mkDeploymentShell {
    e = env;
    r = cfg.region;
    initPass = (initPass env cfg.keys);
    inherit importKeys;
  })
  envs
