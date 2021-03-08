{ pkgs, plutus, marlowe-playground, plutus-playground }:
with pkgs;
let
  # 20.03 version of terraform is broken on some versions of OSX so I have copied the last 0_12 version from nixpkgs
  terraform = (callPackage ./terraform.nix { }).terraform_0_12;

  # This creates a script that will set AWS env vars by getting a session token based on your user name and MFA
  getCreds = pkgs.writeShellScriptBin "getcreds" ''
    set -eou pipefail

    if [[ $# -ne 2 ]]; then
      echo "Please call the script with your AWS account username followed by the MFA code"
      exit 1
    fi
    export AWS_PROFILE=dev-mantis
    unset AWS_SESSION_TOKEN
    unset AWS_SECRET_ACCESS_KEY
    unset AWS_ACCESS_KEY_ID

    ${awscli}/bin/aws sts get-session-token --serial-number "arn:aws:iam::454236594309:mfa/$1" --output text --duration-seconds 86400 --token-code "$2" \
            | awk '{printf("export AWS_ACCESS_KEY_ID=%s\nexport AWS_SECRET_ACCESS_KEY=\"%s\"\nexport AWS_SESSION_TOKEN=\"%s\"\n",$2,$4,$5)}'
  '';

  mkExtraTerraformVars = attrs:
    let
      lines = lib.mapAttrsToList (name: value: "export TF_VAR_${name}=${value}") attrs;
    in
    lib.concatStringsSep "\n" lines;

  refreshTerraform = env: region: { extraTerraformVars ? { } }:
    writeShellScript "refresh" ''
      set -eou pipefail

      tmp_dir=$(mktemp -d)
      echo "using tmp_dir $tmp_dir"

      ln -s ${./terraform}/* "$tmp_dir"

      # in case we have some tfvars around in ./terraform (note: don't use "" as it stops wildcards from working)
      rm $tmp_dir/*.tfvars || true

      cd "$tmp_dir"

      echo "set output directory"
      export TF_VAR_output_path="$tmp_dir"

      echo "read secrets"
      TF_VAR_marlowe_github_client_id=$(pass ${env}/marlowe/githubClientId)
      TF_VAR_marlowe_github_client_secret=$(pass ${env}/marlowe/githubClientSecret)
      TF_VAR_marlowe_jwt_signature=$(pass ${env}/marlowe/jwtSignature)
      TF_VAR_plutus_github_client_id=$(pass ${env}/plutus/githubClientId)
      TF_VAR_plutus_github_client_secret=$(pass ${env}/plutus/githubClientSecret)
      TF_VAR_plutus_jwt_signature=$(pass ${env}/plutus/jwtSignature)

      export TF_VAR_marlowe_github_client_id
      export TF_VAR_marlowe_github_client_secret
      export TF_VAR_marlowe_jwt_signature
      export TF_VAR_plutus_github_client_id
      export TF_VAR_plutus_github_client_secret
      export TF_VAR_plutus_jwt_signature

      # other terraform variables
      export TF_VAR_env="${env}"
      export TF_VAR_aws_region="${region}"
      ${mkExtraTerraformVars extraTerraformVars}

      echo "refresh terraform"
      ${terraform}/bin/terraform init
      ${terraform}/bin/terraform workspace select ${env}
      ${terraform}/bin/terraform refresh
    '';

  applyTerraform = env: region: { extraTerraformVars ? { } }:
    writeShellScript "deploy" ''
      set -eou pipefail

      tmp_dir=$(mktemp -d)
      echo "using tmp_dir $tmp_dir"

      ln -s ${./terraform}/* "$tmp_dir"

      # in case we have some tfvars around in ./terraform (note: don't use "" as it stops wildcards from working)
      rm $tmp_dir/*.tfvars || true

      cd "$tmp_dir"

      echo "set output directory"
      export TF_VAR_output_path="$tmp_dir"

      echo "read secrets"
      TF_VAR_marlowe_github_client_id=$(pass ${env}/marlowe/githubClientId)
      TF_VAR_marlowe_github_client_secret=$(pass ${env}/marlowe/githubClientSecret)
      TF_VAR_marlowe_jwt_signature=$(pass ${env}/marlowe/jwtSignature)
      TF_VAR_plutus_github_client_id=$(pass ${env}/plutus/githubClientId)
      TF_VAR_plutus_github_client_secret=$(pass ${env}/plutus/githubClientSecret)
      TF_VAR_plutus_jwt_signature=$(pass ${env}/plutus/jwtSignature)

      export TF_VAR_marlowe_github_client_id
      export TF_VAR_marlowe_github_client_secret
      export TF_VAR_marlowe_jwt_signature
      export TF_VAR_plutus_github_client_id
      export TF_VAR_plutus_github_client_secret
      export TF_VAR_plutus_jwt_signature

      # other terraform variables
      export TF_VAR_env="${env}"
      export TF_VAR_aws_region="${region}"
      ${mkExtraTerraformVars extraTerraformVars}

      echo "apply terraform"
      ${terraform}/bin/terraform init
      ${terraform}/bin/terraform workspace select ${env} || ${terraform}/bin/terraform workspace new ${env}
      ${terraform}/bin/terraform apply

      echo "json files created in $tmp_dir"

      plutus_tld=$(cat $tmp_dir/machines.json | jq -r '.plutusTld')
      cat > $tmp_dir/secrets.plutus.${env}.env <<EOL
      JWT_SIGNATURE="$(pass ${env}/plutus/jwtSignature)"
      FRONTEND_URL="https://${env}.$plutus_tld"
      GITHUB_CALLBACK_PATH="/#/gh-oauth-cb"
      GITHUB_CLIENT_ID="$(pass ${env}/plutus/githubClientId)"
      GITHUB_CLIENT_SECRET="$(pass ${env}/plutus/githubClientSecret)"
      WEBGHC_URL="https://${env}.$plutus_tld"
      EOL

      marlowe_tld=$(cat $tmp_dir/machines.json | jq -r '.marloweTld')
      cat > $tmp_dir/secrets.marlowe.${env}.env <<EOL
      JWT_SIGNATURE="$(pass ${env}/marlowe/jwtSignature)"
      FRONTEND_URL="https://${env}.$marlowe_tld"
      GITHUB_CALLBACK_PATH="/#/gh-oauth-cb"
      GITHUB_CLIENT_ID="$(pass ${env}/marlowe/githubClientId)"
      GITHUB_CLIENT_SECRET="$(pass ${env}/marlowe/githubClientSecret)"
      EOL

      # This is a nasty way to make deployment with morph easier since I cannot yet find a way to get morph deployments to work
      # from within a nix derivation shell script.
      # Once you have run this script you will have the correct information in the morph directory for morph to deploy to the EC2 instances
      if [[ ! -z "$PLUTUS_ROOT" ]]; then
        echo "copying machine information to $PLUTUS_ROOT/deployment/morph"
        cp $tmp_dir/machines.json $PLUTUS_ROOT/deployment/morph/
        cp $tmp_dir/secrets.plutus.${env}.env $PLUTUS_ROOT/deployment/morph/
        cp $tmp_dir/secrets.marlowe.${env}.env $PLUTUS_ROOT/deployment/morph/
      fi

      # It is important to note that in terraform, a local_file will not be updated if it exists in the location that you define.
      # Since we are using a temporary working directory, the file will always be re-created.
      mkdir -p ~/.ssh/config.d
      cp $tmp_dir/plutus_playground.${env}.conf ~/.ssh/config.d/
    '';

  deploy = env: region: extraParams:
    writeShellScript "deploy" ''
      set -eou pipefail

      ${applyTerraform env region extraParams}
      echo "done"
    '';

  destroy = env: region: { extraTerraformVars ? { } }:
    writeShellScript "destroy" ''
      set -eou pipefail

      tmp_dir=$(mktemp -d)
      echo "using tmp_dir $tmp_dir"

      ln -s ${./terraform}/* "$tmp_dir"

      # in case we have some tfvars around in ./terraform
      rm $tmp_dir/*.tfvars || true

      cd "$tmp_dir"

      echo "set output directory"
      export TF_VAR_output_path="$tmp_dir"

      echo "apply terraform"
      export TF_VAR_marlowe_github_client_id=$(pass ${env}/marlowe/githubClientId)
      export TF_VAR_marlowe_github_client_secret=$(pass ${env}/marlowe/githubClientSecret)
      export TF_VAR_marlowe_jwt_signature=$(pass ${env}/marlowe/jwtSignature)
      export TF_VAR_plutus_github_client_id=$(pass ${env}/plutus/githubClientId)
      export TF_VAR_plutus_github_client_secret=$(pass ${env}/plutus/githubClientSecret)
      export TF_VAR_plutus_jwt_signature=$(pass ${env}/plutus/jwtSignature)

      # other terraform variables
      export TF_VAR_env="${env}"
      export TF_VAR_aws_region="${region}"
      ${mkExtraTerraformVars extraTerraformVars}

      ${terraform}/bin/terraform init
      ${terraform}/bin/terraform workspace select ${env}
      ${terraform}/bin/terraform destroy
    '';

  /* The set of all gpg keys that can be used by pass
     To add a new user, put their key in ./deployment/keys and add the key filename and id here.
     You can cheat the id by putting an empty value and then running `$(nix-build -A deployment.importKeys)`
     and then finding the key id with `gpg --list-keys` and updating this set.
  */
  keys = {
    david = { name = "david.smith.gpg"; id = "97AC81FA54660BD539BE34F0B9D7A61EC23259A6"; };
    kris = { name = "kris.jenkins.gpg"; id = "7EE9B7DE0F3CA25DB5B93D88A1ABC88D19C8136C"; };
    pablo = { name = "pablo.lamela.gpg"; id = "52AB1370A5BB41307470F9B05BA76ACFF04A2ACD"; };
    hernan = { name = "hernan.rajchert.gpg"; id = "AFF6767D33EFF77D519EE6B8C7BBC002683C8DCB"; };
    tobias = { name = "tobias.pflug.gpg"; id = "46681E3759BA8680B3180AA0EBA3115F56AA2315"; };
    amyas = { name = "amyas.merivale.gpg"; id = "8504C0C97F2164419433AAF63F91FB4358BD1137"; };
  };

  /* We store developers public gpg keys in this project so this is a little
     script that imports all the relevant keys.
  */
  importKeys =
    let
      nameToFile = name: ./. + "/keys/${name}";
      keyFiles = lib.mapAttrsToList (name: value: nameToFile value.name) keys;
      lines = map (k: "gpg --import ${k}") keyFiles;
    in
    writeShellScript "import-gpg-keys" (lib.concatStringsSep "\n" lines);

  /* This will change an environment's pass entry to work with specific people's keys
     i.e. If you want to enable a new developer to deploy to a specific environment you
     need to add them to the list of keys for the environment and then re-encrypt with
     this script.
  */
  initPass = env: keys:
    let
      ids = map (k: k.id) keys;
    in
    writeShellScript "init-keys-${env}" ''
      pass init -p ${env} ${lib.concatStringsSep " " ids}
    '';

  mkEnv = env: region: keyNames: extraParams: {
    inherit terraform;
    applyTerraform = (applyTerraform env region extraParams);
    refreshTerraform = (refreshTerraform env region extraParams);
    deploy = (deploy env region extraParams);
    destroy = (destroy env region extraParams);
    initPass = (initPass env keyNames);
  };

  envs = {
    david = mkEnv "david" "sa-east-1" [ keys.david ] {
      extraTerraformVars = { bastion_instance_type = "t3.small"; };
    };
    kris = mkEnv "kris" "eu-west-1" [ keys.kris ] { };
    alpha = mkEnv "alpha" "eu-west-2" [ keys.david keys.kris keys.pablo keys.hernan keys.tobias keys.amyas ] { };
    pablo = mkEnv "pablo" "eu-west-3" [ keys.pablo ] { };
    playground = mkEnv "playground" "us-west-1" [ keys.david keys.kris keys.pablo keys.hernan keys.tobias keys.amyas ] { };
    testing = mkEnv "testing" "eu-west-3" [ keys.david keys.kris keys.pablo keys.hernan keys.tobias keys.amyas ] { };
    hernan = mkEnv "hernan" "us-west-2" [ keys.hernan ] { };
    tobias = mkEnv "tobias" "eu-west-1" [ keys.tobias ] { };
    amyas = mkEnv "amyas" "eu-west-2" [ keys.amyas ] { };
    # this is anything that is defined in $PLUTUS_HOME/infrastructure such as the grafana instance
    global = { initPass = (initPass "global" [ keys.david keys.kris keys.pablo keys.hernan ]); };
  };

  configTest = import ./morph/test.nix;
in
envs // { inherit getCreds static configTest importKeys; }
