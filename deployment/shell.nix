{ system ? builtins.currentSystem
, packages ? import ./.. { }
}:
let
  inherit (packages) pkgs;
  inherit (pkgs) terraform awscli mkShell writeShellScriptBin pass lib morph;
  inherit (pkgs.stdenv) isDarwin;

  e = "tobias";
  r = "eu-west-1";

  # setupEnvSecrets : Set environment variables with secrets from pass
  # for `env` and `region`.
  setupEnvSecrets = env: ''
    # Set the password store
    export PASSWORD_STORE_DIR="$(pwd)/../secrets"

    # Set up environment we want to work on

    # Set up secrets for the environment
    export TF_VAR_marlowe_github_client_id=$(pass ${env}/marlowe/githubClientId)
    export TF_VAR_marlowe_github_client_secret=$(pass ${env}/marlowe/githubClientSecret)
    export TF_VAR_marlowe_jwt_signature=$(pass ${env}/marlowe/jwtSignature)
    export TF_VAR_plutus_github_client_id=$(pass ${env}/plutus/githubClientId)
    export TF_VAR_plutus_github_client_secret=$(pass ${env}/plutus/githubClientSecret)
    export TF_VAR_plutus_jwt_signature=$(pass ${env}/plutus/jwtSignature)
  '';

  # setupTerraform : Switch to `env` workspace (create it if neccessary)
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

  # deploy-nix: wrapper around executing `morph deploy` which ensures that
  # terraform is up to date.
  deployNix = writeShellScriptBin "deploy-nix" ''
    set -eou pipefail

    echo "[deploy-nix]: Checking if terraform state is up to date"
    if ! terraform plan --detailed-exitcode -compact-warnings ./terraform >/dev/null ; then
      echo "[deploy-nix]: terraform state is not up to date - Aborting"
      exit 1
    fi

    # TODO: Extract secrets from machines.json

    echo "[deploy-nix]: Starting deployment ..."
    ${morph}/bin/morph deploy ./morph/default.nix switch
  '';


  # getCreds : Log in to AWS using MFA
  # Sets the following variables:
  # - AWS_PROFILE
  # - AWS_SESSION_TOKEN
  # - AWS_SECRET_ACCESS_KEY
  # - AWS_ACCESS_KEY_ID
  aws-mfa-login = writeShellScriptBin "aws-mfa-login" ''
    set -eou pipefail

    if [[ $# -ne 2 ]]; then
      echo "Please call the script with your AWS account username followed by the MFA code"
      exit 1
    fi
    export AWS_PROFILE=dev-mantis
    unset AWS_SESSION_TOKEN
    unset AWS_SECRET_ACCESS_KEY
    unset AWS_ACCESS_KEY_ID

    read AWS_ACCESS_KEY_ID AWS_SECRET_ACCESS_KEY AWS_SESSION_TOKEN <<< \
      $(${awscli}/bin/aws sts get-session-token --serial-number "arn:aws:iam::454236594309:mfa/$1" \
                                                --output text \
                                                --duration-seconds 86400 \
                                                --token-code "$2" \
                                                | awk '{ print $2 $4 $5 }')
    ${awscli}/bin/aws sts get-caller-identity
  '';
in
mkShell {
  buildInputs = [ terraform aws-mfa-login pass deployNix ];
  shellHook = ''
    ${setupEnvSecrets e}
    ${setupTerraform e r}

    echo "---------------------------------------------------------------------"
    echo "deployment shell for '${e}'"
    echo "---------------------------------------------------------------------"
    echo "Available commands:"
    echo ""
    echo -e "\t* aws-mfa-login:    login to aws"
    echo -e "\t* provision-infra:  provision infrastructure"
    echo -e "\t* deploy-nix:       deploy nix configuration to infrastructure"
    echo -e "\t* deploy:           provision infrastructure and deploy nix configuration"
    echo -e ""
    echo "Notes:"
    echo ""
    echo "- Running 'aws-mfa-login' is a prerequisite to all commands"
    echo "- The './terraform' dir has to be specified to run arbitrary terraform commands"
  '' + lib.optionalString (isDarwin) ''echo "- Deploying on macOS requires a remote builder to work"'';
}
