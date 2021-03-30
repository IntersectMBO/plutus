{ pkgs ? (import ./.. { }).pkgs }:
let
  inherit (pkgs) writeShellScriptBin lib mkShell stdenv;
  inherit (pkgs) awscli pass terraform morph jq;

  # { user -> { name, id } }
  keys = import ./keys.nix;

  # The set of all gpg keys that can be used by pass
  # To add a new user, put their key in ./deployment/keys and add the key filename and id here.
  # You can cheat the id by putting an empty value and then running `$(nix-build -A deployment.importKeys)`
  # and then finding the key id with `gpg --list-keys` and updating this set.
  envs = import ./envs.nix { inherit keys; };

  # importKeys : create a shell-script that imports all specified keys
  # - k: keys to import
  importKeys = ks:
    let
      nameToFile = name: ./. + "/keys/${name}";
      keyFiles = lib.mapAttrsToList (name: value: nameToFile value.name) ks;
      lines = map (k: "gpg --import ${k}") keyFiles;
    in
    writeShellScriptBin "import-gpg-keys" (lib.concatStringsSep "\n" lines);

  # initPass: This will change an environment's pass entry to work with specific people's keys
  # i.e. If you want to enable a new developer to deploy to a specific environment you
  # need to add them to the list of keys for the environment and then re-encrypt with
  # this script.
  initPass = env: keys:
    let
      ids = map (k: k.id) (builtins.attrValues keys);
    in
    writeShellScriptBin "init-keys-${env}" ''
      ${pass}/bin/pass init -p ${env} ${lib.concatStringsSep " " ids}
    '';


  # keyInitShell: convenience shell for simply importing all existing keys
  # ```
  # $ nix-shell -A importKeys
  # ```
  keyInitShell = mkShell {
    shellHook = ''
      ${importKeys keys}/bin/import-gpg-keys
      exit 0
    '';
  };

  # mkDeploymentShell : Provide a deployment shell for a specific environment
  # The shell expects to be executed from within the `deployment` directory and will
  # not work when invoked from elsewhere.
  mkDeploymentShell =
    { env        # environment to work on
    , region     # region to deploy to
    , keys       # keys lookup map
    }:
    let
      # importKeys: crate environment specific key-import script
      importEnvKeys = importKeys keys;

      # initEnvPass: crate 'pass' initialization script for this environment
      initEnvPass = initPass env keys;


      # setupEnvSecrets : Set environment variables with secrets from pass
      # - env: Environment to setup
      setupEnvSecrets = env: ''
        # Set the password store
        export PASSWORD_STORE_DIR="$(pwd)/../secrets"

        # Set up environment we want to work on
        export DEPLOYMENT_ENV="${env}"

        # Set up secrets for the environment
        export TF_VAR_marlowe_github_client_id=$(${pass}/bin/pass ${env}/marlowe/githubClientId)
        export TF_VAR_marlowe_github_client_secret=$(${pass}/bin/pass ${env}/marlowe/githubClientSecret)
        export TF_VAR_marlowe_jwt_signature=$(${pass}/bin/pass ${env}/marlowe/jwtSignature)
        export TF_VAR_plutus_github_client_id=$(${pass}/bin/pass ${env}/plutus/githubClientId)
        export TF_VAR_plutus_github_client_secret=$(${pass}/bin/pass ${env}/plutus/githubClientSecret)
        export TF_VAR_plutus_jwt_signature=$(${pass}/bin/pass ${env}/plutus/jwtSignature)
      '';

      # setupTerraform : Switch to `env` workspace (create it if neccessary)
      # - env: environment to work on
      # - region: region the environment is in
      setupTerraform = env: region: ''
        export TF_VAR_env="${env}"
        export TF_VAR_aws_region="${region}"
        export TF_VAR_output_path=$(pwd)

        ${terraform}/bin/terraform init ./terraform
        if ! ${terraform}/bin/terraform workspace list ./terraform | grep -q ${env} ; then
          ${terraform}/bin/terraform workspace new ${env} ./terraform
          ${terraform}/bin/terraform workspace select ${env} ./terraform
        else
          ${terraform}/bin/terraform workspace select ${env} ./terraform
        fi
      '';

      # provisionInfra: Apply a terraform configuration
      # Provision the current environment.
      provisionInfra = writeShellScriptBin "provision-infra" ''
        set -eou pipefail

        echo "[provision-infra]: Provisioning infrastructure using terraform"
        ${terraform}/bin/terraform apply -auto-approve ./terraform
      '';

      # destroyInfra: Destroy any existing infrastructure via terraform
      destroyInfra = writeShellScriptBin "destroy-infra" ''
        set -eou pipefail

        echo "[provision-infra]: Destroying infrastructure using terraform"
        ${terraform}/bin/terraform destroy ./terraform
      '';

      # deploy-nix: wrapper around executing `morph deploy` 
      # - Checks if `machines.json` is present - aborts if not
      # - Checks if terraform is up to date - aborts if not
      # - Writes ssh configuration and copies secrets to the morph config directory
      deployNix = writeShellScriptBin "deploy-nix" ''
        set -eou pipefail

        # In order to ensure a consistent state we verify that terraform
        # reports it has nothing to do before we even attempt to deploy
        # any nix configuration.

        echo "[deploy-nix]: Checking if terraform state is up to date"
        if ! ${terraform}/bin/terraform plan --detailed-exitcode -compact-warnings ./terraform >/dev/null ; then
          echo "[deploy-nix]: terraform state is not up to date - Aborting"
          exit 1
        fi

        # morph needs info about the ec2 instances that were created by terraform.
        # This bridge is provided by `machines.json` which is a local resource created
        # by terraform in `deployment/terraform/machines.tf`.

        if ! [ -f ./machines.json ]; then
          echo "[deploy-nix]: machines.json is not present. Aborting."
          exit 1
        fi
        echo "[deploy-nix]: copying machines.json .."
        cp ./machines.json ./morph

        if [ -z "$DEPLOYMENT_ENV" ]; then
          echo "[deploy-nix]: Error, 'DEPLOYMENT_ENV' is not set! Aborting."
          exit 1
        fi

        # morph needs access to environment-specific secrets which
        # are retrieved via `pass` and written to files in the morph directory.

        echo "[deploy-nix]: Writing plutus secrets ..."
        plutus_tld=$(cat ./machines.json | ${jq}/bin/jq -r '.plutusTld')
        cat > ./morph/secrets.plutus.$DEPLOYMENT_ENV.env <<EOL
        export JWT_SIGNATURE="$(pass $DEPLOYMENT_ENV/plutus/jwtSignature)"
        export GITHUB_CLIENT_ID="$(pass $DEPLOYMENT_ENV/plutus/githubClientId)"
        export GITHUB_CLIENT_SECRET="$(pass $DEPLOYMENT_ENV/plutus/githubClientSecret)"
        EOL

        echo "[deploy-nix]: Writing marlowe secrets ..."
        marlowe_tld=$(cat ./machines.json | ${jq}/bin/jq -r '.marloweTld')
        cat > ./morph/secrets.marlowe.$DEPLOYMENT_ENV.env <<EOL
        JWT_SIGNATURE="$(pass $DEPLOYMENT_ENV/marlowe/jwtSignature)"
        export GITHUB_CLIENT_ID="$(pass $DEPLOYMENT_ENV/marlowe/githubClientId)"
        export GITHUB_CLIENT_SECRET="$(pass $DEPLOYMENT_ENV/marlowe/githubClientSecret)"
        EOL

        # in order for morph to be able to access any of the machines
        # at all we need to install an ssh configuration file.
        # --------------------------------------------------------------
        # NOTE: THIS WILL MODIFY FILES IN YOUR `~/.ssh/config` DIRECTORY
        # --------------------------------------------------------------

        echo "[deploy-nix]: Installing ssh configuration ..."
        mkdir -p ~/.ssh/config.d
        cp plutus_playground.$DEPLOYMENT_ENV.conf ~/.ssh/config.d/

        echo "[deploy-nix]: Starting deployment ..."
        ${morph}/bin/morph deploy --upload-secrets ./morph/default.nix switch
      '';

      # deploy: combine terraform provisioning and morph deployment
      deploy = writeShellScriptBin "deploy" ''
        ${provisionInfra}/bin/provision-infra
        ${deployNix}/bin/deploy-nix
      '';

    in
    mkShell {
      buildInputs = [ importEnvKeys initEnvPass terraform pass deployNix provisionInfra destroyInfra deploy ];
      shellHook = ''
        if ! ${awscli}/bin/aws sts get-caller-identity 2>/dev/null ; then
          echo "Error: Not logged in to aws. Aborting"
          echo "Use 'eval \$(aws-mfa-login <user> <code>)' to log in"
          exit 1
        fi

        ${setupEnvSecrets env}
        ${setupTerraform env region}

        echo "---------------------------------------------------------------------"
        echo "deployment shell for '${env}'"
        echo "---------------------------------------------------------------------"
        echo "Available commands:"
        echo ""
        echo -e "\t* provision-infra:  provision infrastructure"
        echo -e "\t* destroy-infra:    destroy the infrastructure completely"
        echo -e "\t* deploy-nix:       deploy nix configuration to infrastructure"
        echo -e "\t* deploy:           provision infrastructure and deploy nix configuration"
        echo ""
        echo "Key handling"
        echo ""
        echo -e "\t* import-gpg-keys:  import all relevant gpg keys"
        echo -e "\t* init-keys-${env}:   allow configured keys access to this environment"
        echo -e ""
        echo "Notes:"
        echo ""
        echo "- Being logged in to aws via 'aws-mfa-login' is a prerequisite to all infrastructure commands"
        echo "- The './terraform' dir has to be specified to run arbitrary terraform commands (e.g. 'terraform plan ./terraform')"
        echo "- The './morph/configurations.nix' file has to be specified to run arbitrary morph commands (e.g. 'morph build ./morph/configurations.nix) "
      '' + lib.optionalString (stdenv.isDarwin) ''echo "- Deploying on macOS requires a remote builder to work"'';
    };
in
# provide a shell for each entry in `env` (use `nix-shell -A env` to enter)
builtins.mapAttrs
  (env: cfg: mkDeploymentShell {
    region = cfg.region;
    inherit env;
    inherit keys;
  })
  envs // { importKeys = keyInitShell; }
