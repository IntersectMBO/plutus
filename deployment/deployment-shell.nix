{ terraform
, awscli
, mkShell
, writeShellScriptBin
, pass
, lib
, morph
, jq
, stdenv
}:

# mkDeploymentShell : Provide a deployment shell for a specific environment
#
# Returns shell environment for
# - provisioning, deploying and destroying infrastructure
# - password initialization
#
# NOTE: The shell expects to be executed from within the `deployment` directory and will
# not work when invoked from elsewhere.

{ e          # environment to work on
, r          # region to deploy to
, initPass   # init secrets for environment
, importKeys # script to import all relevant keys
}:
let
  # setupEnvSecrets : Set environment variables with secrets from pass
  # - env: Environment to setup
  setupEnvSecrets = env: ''
    # Set the password store
    export PASSWORD_STORE_DIR="$(pwd)/../secrets"

    # Set up environment we want to work on
    export DEPLOYMENT_ENV="${env}"

    # Set up secrets for the environment
    export TF_VAR_marlowe_github_client_id=$(pass ${env}/marlowe/githubClientId)
    export TF_VAR_marlowe_github_client_secret=$(pass ${env}/marlowe/githubClientSecret)
    export TF_VAR_marlowe_jwt_signature=$(pass ${env}/marlowe/jwtSignature)
    export TF_VAR_plutus_github_client_id=$(pass ${env}/plutus/githubClientId)
    export TF_VAR_plutus_github_client_secret=$(pass ${env}/plutus/githubClientSecret)
    export TF_VAR_plutus_jwt_signature=$(pass ${env}/plutus/jwtSignature)
  '';

  # setupTerraform : Switch to `env` workspace (create it if neccessary)
  # - env: environment to work on
  # - region: region the environment is in
  setupTerraform = env: region: ''
    export TF_VAR_env="${env}"
    export TF_VAR_aws_region="${region}"
    export TF_VAR_output_path=$(pwd)

    terraform init ./terraform
    if ! terraform workspace list ./terraform | grep -q ${env} ; then
      terraform workspace new ${env} ./terraform
      terraform workspace select ${env} ./terraform
    else
      terraform workspace select ${env} ./terraform
    fi
  '';

  # provisionInfra: Apply a terraform configuration
  # Provision the current environment.
  provisionInfra = writeShellScriptBin "provision-infra" ''
    set -eou pipefail

    echo "[provision-infra]: Provisioning infrastructure using terraform"
    terraform apply ./terraform
  '';

  destroyInfra = writeShellScriptBin "destroy-infra" ''
    set -eou pipefail

    echo "[provision-infra]: Destroying infrastructure using terraform"
    terraform destroy ./terraform
  '';

  # deploy-nix: wrapper around executing `morph deploy` 
  # - Checks if `machines.json` is present - aborts if not
  # - Checks if terraform is up to date - aborts if not
  # - Writes ssh configuration and copies secrets to the morph config directory
  deployNix = writeShellScriptBin "deploy-nix" ''
    set -eou pipefail

    echo "[deploy-nix]: Checking if terraform state is up to date"
    if ! terraform plan --detailed-exitcode -compact-warnings ./terraform >/dev/null ; then
      echo "[deploy-nix]: terraform state is not up to date - Aborting"
      exit 1
    fi

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

    echo "[deploy-nix]: Writing secrets ..."
    plutus_tld=$(cat ./machines.json | ${jq}/bin/jq -r '.plutusTld')
    cat > ./morph/secrets.plutus.$DEPLOYMENT_ENV.env <<EOL
    JWT_SIGNATURE="$(pass $DEPLOYMENT_ENV/plutus/jwtSignature)"
    FRONTEND_URL="https://$DEPLOYMENT_ENV.$plutus_tld"
    GITHUB_CALLBACK_PATH="/#/gh-oauth-cb"
    GITHUB_CLIENT_ID="$(pass $DEPLOYMENT_ENV/plutus/githubClientId)"
    GITHUB_CLIENT_SECRET="$(pass $DEPLOYMENT_ENV/plutus/githubClientSecret)"
    WEBGHC_URL="https://$DEPLOYMENT_ENV.$plutus_tld"
    EOL

    marlowe_tld=$(cat ./machines.json | ${jq}/bin/jq -r '.marloweTld')
    cat > ./morph/secrets.marlowe.$DEPLOYMENT_ENV.env <<EOL
    JWT_SIGNATURE="$(pass $DEPLOYMENT_ENV/marlowe/jwtSignature)"
    FRONTEND_URL="https://$DEPLOYMENT_ENV.$marlowe_tld"
    GITHUB_CALLBACK_PATH="/#/gh-oauth-cb"
    GITHUB_CLIENT_ID="$(pass $DEPLOYMENT_ENV/marlowe/githubClientId)"
    GITHUB_CLIENT_SECRET="$(pass $DEPLOYMENT_ENV/marlowe/githubClientSecret)"
    EOL

    echo "[deploy-nix]: Installing ssh configuration ..."
    mkdir -p ~/.ssh/config.d
    cp plutus_playground.$DEPLOYMENT_ENV.conf ~/.ssh/config.d/

    echo "[deploy-nix]: Starting deployment ..."
    ${morph}/bin/morph deploy --upload-secrets ./morph/default.nix switch
  '';


in
mkShell {
  buildInputs = [ importKeys initPass terraform pass deployNix provisionInfra destroyInfra ];
  shellHook = ''
    if ! ${awscli}/bin/aws sts get-caller-identity 2>/dev/null ; then
      echo "Error: Not logged in to aws. Aborting"
      echo "Use 'eval \$(aws-mfa-login <user> <code>)' to log in"
      exit 1
    fi

    ${setupEnvSecrets e}
    ${setupTerraform e r}

    echo "---------------------------------------------------------------------"
    echo "deployment shell for '${e}'"
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
    echo -e "\t* init-keys-${e}:   allow configured keys access to this environment"
    echo -e ""
    echo "Notes:"
    echo ""
    echo "- Being logged in to aws via 'aws-mfa-login' is a prerequisite to all infrastructure commands"
    echo "- The './terraform' dir has to be specified to run arbitrary terraform commands (e.g. 'terraform plan ./terraform')"
    echo "- The './morph/configurations.nix' file has to be specified to run arbitrary morph commands (e.g. 'morph build ./morph/configurations.nix) "
  '' + lib.optionalString (stdenv.isDarwin) ''echo "- Deploying on macOS requires a remote builder to work"'';
}
