{ pkgs ? (import ./.. { }).pkgs
, rev ? "dev"
}:
let
  inherit (pkgs) writeShellScriptBin lib mkShell stdenv writeText;
  inherit (pkgs) awscli terraform morph jq;
  inherit (pkgs.gitAndTools) hub;

  # All environments and the region they are in
  envs = import ./envs.nix;

  # mkDeploymentShell : Provide a deployment shell for a specific environment
  # The shell expects to be executed from within the `deployment` directory and will
  # not work when invoked from elsewhere.
  mkDeploymentShell =
    { env         # environment to work on
    , region      # region to deploy to
    , rev ? "dev" # git revision being deployed
    }:
    let
      # setupEnvSecrets : Set environment variables with secrets from pass
      # - env: Environment to setup
      setupEnvSecrets = env: ''
        export DEPLOYMENT_ENV="${env}"

        SECRETS=$(${awscli}/bin/aws secretsmanager get-secret-value --secret env/${env} --query SecretString --output text --region ${region})
        export TF_VAR_marlowe_github_client_id=$(echo $SECRETS | ${jq}/bin/jq ".marlowe.githubClientId")
        export TF_VAR_marlowe_github_client_secret=$(echo $SECRETS | ${jq}/bin/jq ".marlowe.githubClientSecret")
        export TF_VAR_marlowe_jwt_signature=$(echo $SECRETS | ${jq}/bin/jq ".marlowe.jwtSignature")
        export TF_VAR_plutus_github_client_id=$(echo $SECRETS | ${jq}/bin/jq ".plutus.githubClientId")
        export TF_VAR_plutus_github_client_secret=$(echo $SECRETS | ${jq}/bin/jq ".plutus.githubClientSecret")
        export TF_VAR_plutus_jwt_signature=$(echo $SECRETS | ${jq}/bin/jq ".plutus.jwtSignature")
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

      # wait-github-status: wait until the current commit has been processed by hydra
      # - checks the github status in a loop with 30s breaks until it is is "success"
      #
      # The `hub ci-status` calls do not seem to get rate limited. This was verified
      # via `curl -H "Accept: application/vnd.github.v3+json" https://api.github.com/rate_limit`
      waitGitHubStatus = writeShellScriptBin "wait-github-status" ''
        set -eou pipefail

        echo "[wait-github-status]: waiting for commit to get processed by hydra"

        SLEEP_SECS=60
        GH_STATUS=$(${hub}/bin/hub ci-status)

        while [ $GH_STATUS != "success" ]; do
         case "$GH_STATUS" in
          failure|error|action_required|cancelled|timed_out)
            echo "[wait-github-status]: $GH_STATUS"
            exit 1
            ;;
          pending)
            pritnf "."
            sleep $SLEEP_SECS
            GH_STATUS=$(${hub}/bin/hub ci-status)
            continue
            ;;
          *)
            echo "[wait-github-status]: Unexpected status $GH_STATUS"
            exit 1
            ;;

         esac
        done
        echo "[wait-github-status]: $GH_STATUS"
        exit 0
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

        # The local files (ssh configuration and dns/ip information on ec2
        # instances) is part of the state so we have to create these before
        # we check if the state is up to date
        echo "[deploy-nix]: Creating terraform bridge files"
        rm -rf ./plutus_playground.$DEPLOYMENT_ENV.conf
        rm -rf ./machines.json
        ${terraform}/bin/terraform apply -auto-approve -target=local_file.ssh_config -target=local_file.machines ./terraform/

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
        cat ./machines.json | jq --arg rev ${rev} '. + {rev: $rev}' > ./morph/machines.json

        if [ -z "$DEPLOYMENT_ENV" ]; then
          echo "[deploy-nix]: Error, 'DEPLOYMENT_ENV' is not set! Aborting."
          exit 1
        fi

        # Create secrets files which are uploaded using morph secrets
        # feature.

        echo "[deploy-nix]: Writing plutus secrets ..."
        plutus_tld=$(cat ./machines.json | ${jq}/bin/jq -r '.plutusTld')
        cat > ./morph/secrets.plutus.$DEPLOYMENT_ENV.env <<EOL
        export JWT_SIGNATURE="$(echo $TF_VAR_plutus_jwt_signature)"
        export GITHUB_CLIENT_ID="$(echo $TF_VAR_plutus_github_client_id)"
        export GITHUB_CLIENT_SECRET="$(echo $TF_VAR_plutus_github_client_secret)"
        EOL

        echo "[deploy-nix]: Writing marlowe secrets ..."
        marlowe_tld=$(cat ./machines.json | ${jq}/bin/jq -r '.marloweTld')
        cat > ./morph/secrets.marlowe.$DEPLOYMENT_ENV.env <<EOL
        export JWT_SIGNATURE="$(echo $TF_VAR_marlowe_jwt_signature)"
        export GITHUB_CLIENT_ID="$(echo $TF_VAR_marlowe_github_client_id)"
        export GITHUB_CLIENT_SECRET="$(echo $TF_VAR_marlowe_github_client_secret)"
        EOL

        #
        # Note: there appears to be some timing issue with how morph executes
        # the health-checks. In order to circumvent this we split these steps in two
        # 1. deployment without health-checks
        # 2. health-checks only
        #
        echo "[deploy-nix]: Starting deployment ..."
        export SSH_SKIP_HOST_KEY_CHECK=1
        export SSH_CONFIG_FILE=./plutus_playground.$DEPLOYMENT_ENV.conf
        ${morph}/bin/morph deploy --skip-health-checks --upload-secrets ./morph/network.nix switch
        ${morph}/bin/morph check-health ./morph/network.nix
      '';

      # deploy: combine terraform provisioning and morph deployment
      deploy = writeShellScriptBin "deploy" ''
        ${provisionInfra}/bin/provision-infra
        ${deployNix}/bin/deploy-nix
      '';

    in
    mkShell {
      buildInputs = [ terraform deployNix provisionInfra destroyInfra deploy waitGitHubStatus ];
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
    inherit env rev;
  })
  envs
