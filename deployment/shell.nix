{ system ? builtins.currentSystem
, packages ? import ./.. { }
}:
let
  inherit (packages) pkgs;
  inherit (pkgs) terraform awscli mkShell writeShellScriptBin pass;

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

  # getCreds : Log in to AWS using MFA
  # this will set the following variables:
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
  buildInputs = [ terraform aws-mfa-login pass ];
  shellHook = ''
    echo "---------------------------------------------------------------------"
    echo "-- deployment shell for '${e}'"
    echo "---------------------------------------------------------------------"
    ${setupEnvSecrets e}
    ${setupTerraform e r}

    echo "---------------------------------------------------------------------"
    echo "-- Use 'aws-mfa-login <aws user> <mfa code>' to login to AWS"
    echo "---------------------------------------------------------------------"

  '';
}
