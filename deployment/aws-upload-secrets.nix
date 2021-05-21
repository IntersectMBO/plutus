{ pkgs ? (import ./.. { }).pkgs
, env
}:
let
  inherit (pkgs) mkShell writeShellScriptBin pass awscli;
  aws-upload-secrets = env:
    let
      region = (import ./envs.nix)."${env}".region;
    in
    writeShellScriptBin "aws-upload-secrets" ''
      set -eo pipefail

      if [ $# -ne 1 ]; then
        echo "[aws-upload-secrets]: Error, Please specify a json file as input"
        exit 1
      fi

      SECRETS_FILE="$1"

      echo "[aws-upload-secrets]: Validating input file '$SECRETS_FILE'"
      cat $SECRETS_FILE | jq empty
      echo "[aws-upload-secrets]: Uploading secrets for '${env}' in region '${region}'"

      ${awscli}/bin/aws secretsmanager create-secret --name "env/${env}" \
        --description "env/${env}" \
        --secret-string file://$SECRETS_FILE \
        --region ${region}
    '';
in
mkShell {
  buildInputs = [ (aws-upload-secrets env) ];
}
