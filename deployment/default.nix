{ pkgs, plutus, marlowe-playground, plutus-playground, marlowe-symbolic-lambda, marlowe-playground-lambda, plutus-playground-lambda }:
with pkgs;
let
  # 20.03 version of terraform is broken on some versions of OSX so I have copied the last 0_12 version from nixpkgs
  terraform = (callPackage ./terraform.nix { }).terraform_0_12;

  # We want to combine clients and tutorials in one directory so that we can sync one folder with S3
  static = {
    plutus = pkgs.runCommand "plutus" { } ''
      mkdir -p $out/tutorial
      find ${plutus-playground.client} -mindepth 1 -maxdepth 1 -exec ln -s -t $out {} +
      find ${plutus-playground.tutorial} -mindepth 1 -maxdepth 1 -exec ln -s -t $out/tutorial {} +
    '';
    marlowe = pkgs.runCommand "marlowe" { } ''
      mkdir -p $out/tutorial
      find ${marlowe-playground.client} -mindepth 1 -maxdepth 1 -exec ln -s -t $out {} +
      find ${marlowe-playground.tutorial} -mindepth 1 -maxdepth 1 -exec ln -s -t $out/tutorial {} +
    '';
  };

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

  terraform-locals = env:
    writeTextFile {
      name = "terraform-locals";
      destination = "/generated.tf.json";
      text = (builtins.toJSON {
        locals = { marlowe_client = "${marlowe-playground.client}"; };
      });
    };

  terraform-vars = env: region:
    writeTextFile {
      name = "terraform-vars";
      destination = "/${env}.tfvars";
      text = ''
        env="${env}"
        aws_region="${region}"
        symbolic_lambda_file="${marlowe-symbolic-lambda}/marlowe-symbolic.zip"
        playground_lambda_file="${marlowe-playground-lambda}/marlowe-playground-lambda.zip"
        plutus_playground_lambda_file="${plutus-playground-lambda}/plutus-playground-lambda.zip"'';
    };

  syncS3 = env: region:
    writeShellScript "syncs3" ''
      set -eou pipefail

      export AWS_REGION=${region}

      echo "sync with S3"
      ${plutus.thorp}/bin/thorp -b marlowe-playground-website-${env} -s ${static.marlowe}
      ${plutus.thorp}/bin/thorp -b plutus-playground-website-${env} -s ${static.plutus}
    '';

  refreshTerraform = env: region:
    writeShellScript "refresh" ''
      set -eou pipefail

      tmp_dir=$(mktemp -d)
      echo "using tmp_dir $tmp_dir"

      ln -s ${./terraform}/* "$tmp_dir"

      # in case we have some tfvars around in ./terraform (note: don't use "" as it stops wildcards from working)
      rm $tmp_dir/*.tfvars || true

      ln -s ${terraform-locals env}/* "$tmp_dir"
      ln -s ${terraform-vars env region}/* "$tmp_dir"
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

      echo "refresh terraform"
      ${terraform}/bin/terraform init
      ${terraform}/bin/terraform workspace select ${env}
      ${terraform}/bin/terraform refresh -var-file=${env}.tfvars
    '';

  applyTerraform = env: region:
    writeShellScript "deploy" ''
      set -eou pipefail

      tmp_dir=$(mktemp -d)
      echo "using tmp_dir $tmp_dir"

      ln -s ${./terraform}/* "$tmp_dir"

      # in case we have some tfvars around in ./terraform (note: don't use "" as it stops wildcards from working)
      rm $tmp_dir/*.tfvars || true

      ln -s ${terraform-locals env}/* "$tmp_dir"
      ln -s ${terraform-vars env region}/* "$tmp_dir"
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

      echo "apply terraform"
      ${terraform}/bin/terraform init
      ${terraform}/bin/terraform workspace select ${env}
      ${terraform}/bin/terraform apply -var-file=${env}.tfvars

      marlowe_api_id=$(${terraform}/bin/terraform output marlowe_rest_api_id)
      plutus_api_id=$(${terraform}/bin/terraform output plutus_rest_api_id)
      region=$(${terraform}/bin/terraform output region)

      echo "deploy api"
      ${awscli}/bin/aws apigateway create-deployment --region "$region" --rest-api-id "$marlowe_api_id" --stage-name ${env}
      ${awscli}/bin/aws apigateway create-deployment --region "$region" --rest-api-id "$plutus_api_id" --stage-name ${env}

      echo "json files created in $tmp_dir"

      # This is a nasty way to make deployment with morph easier since I cannot yet find a way to get morph deployments to work 
      # from within a nix derivation shell script. 
      # Once you have run this script you will have the correct information in the morph directory for morph to deploy to the EC2 instances
      if [[ ! -z "$PLUTUS_ROOT" ]]; then
        echo "copying machine information to $PLUTUS_ROOT/deployment/morph"
        cp $tmp_dir/machines.json $PLUTUS_ROOT/deployment/morph/
      fi
    '';

  deploy = env: region:
    writeShellScript "deploy" ''
      set -eou pipefail

      ${applyTerraform env region}
      ${syncS3 env region}
      echo "done"
    '';

  destroy = env: region:
    writeShellScript "destroy" ''
      set -eou pipefail

      tmp_dir=$(mktemp -d)
      echo "using tmp_dir $tmp_dir"

      ln -s ${./terraform}/* "$tmp_dir"

      # in case we have some tfvars around in ./terraform
      rm $tmp_dir/*.tfvars || true

      ln -s ${terraform-locals env}/* "$tmp_dir"
      ln -s ${terraform-vars env region}/* "$tmp_dir"
      cd "$tmp_dir"

      echo "apply terraform"
      export TF_VAR_marlowe_github_client_id=$(pass ${env}/marlowe/githubClientId)
      export TF_VAR_marlowe_github_client_secret=$(pass ${env}/marlowe/githubClientSecret)
      export TF_VAR_marlowe_jwt_signature=$(pass ${env}/marlowe/jwtSignature)
      export TF_VAR_plutus_github_client_id=$(pass ${env}/plutus/githubClientId)
      export TF_VAR_plutus_github_client_secret=$(pass ${env}/plutus/githubClientSecret)
      export TF_VAR_plutus_jwt_signature=$(pass ${env}/plutus/jwtSignature)
      ${terraform}/bin/terraform init
      ${terraform}/bin/terraform workspace select ${env}
      ${terraform}/bin/terraform destroy -var-file=${env}.tfvars
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

  mkEnv = env: region: keyNames: {
    inherit terraform-vars terraform-locals terraform;
    syncS3 = (syncS3 env region);
    applyTerraform = (applyTerraform env region);
    refreshTerraform = (refreshTerraform env region);
    deploy = (deploy env region);
    destroy = (destroy env region);
    initPass = (initPass env keyNames);
  };

  envs = {
    david = mkEnv "david" "eu-west-1" [ keys.david ];
    kris = mkEnv "kris" "eu-west-1" [ keys.kris ];
    alpha = mkEnv "alpha" "eu-west-2" [ keys.david keys.kris keys.pablo ];
    pablo = mkEnv "pablo" "eu-west-3" [ keys.pablo ];
    playground = mkEnv "playground" "us-west-1" [ keys.david keys.kris keys.pablo ];
    wyohack = mkEnv "wyohack" "us-west-2" [ keys.david keys.kris keys.pablo ];
    testing = mkEnv "testing" "eu-west-3" [ keys.david keys.kris keys.pablo ];
  };

  configTest = import ./morph/test.nix;
in
envs // { inherit getCreds static configTest importKeys; }
