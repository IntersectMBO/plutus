{ pkgs, marlowe-playground, marlowe-symbolic-lambda, marlowe-playground-lambda }:
with pkgs;
let
  # 20.03 version of terraform is broken on some versions of OSX so I have copied the last 0_12 version from nixpkgs
  terraform = (callPackage ./terraform.nix { }).terraform_0_12;

  getCreds = pkgs.writeShellScript "getcreds" ''
    if [[ $# -ne 2 ]]; then
      echo "Please call the script with your AWS account username followed by the MFA code"
      exit 1
    fi
    export AWS_PROFILE=dev-mantis
    unset AWS_SESSION_TOKEN
    unset AWS_SECRET_ACCESS_KEY
    unset AWS_ACCESS_KEY_ID

    ${awscli}/bin/aws sts get-session-token --serial-number arn:aws:iam::454236594309:mfa/$1 --output text --duration-seconds 86400 --token-code $2 \
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
      '' + (if pkgs.stdenv.isDarwin then
      # On OSX you need to set the env vars with the locations of the lambda zip files e.g.
      # export TF_VAR_symbolic_lambda_file=/path/to/marlowe-symbolic.zip
      # export TF_VAR_playground_lambda_file=/path/to/marlowe-playground-lambda.zip
        ""
      else
        ''
          symbolic_lambda_file="${marlowe-symbolic-lambda}/marlowe-symbolic.zip"
          playground_lambda_file="${marlowe-playground-lambda}/marlowe-playground-lambda.zip"'');
    };

  runTerraform = env: region:
    writeShellScript "terraform" ''
      tmp_dir=$(mktemp -d)
      ln -s ${./terraform}/* $tmp_dir
      ln -s ${terraform-locals env}/* $tmp_dir
      ln -s ${terraform-vars env region}/* $tmp_dir
      cd $tmp_dir
      export TF_VAR_marlowe_github_client_id=$(pass ${env}/marlowe/githubClientId)
      export TF_VAR_marlowe_github_client_secret=$(pass ${env}/marlowe/githubClientSecret)
      export TF_VAR_marlowe_jwt_signature=$(pass ${env}/marlowe/jwtSignature)
      ${terraform}/bin/terraform init
      ${terraform}/bin/terraform workspace select ${env}
      ${terraform}/bin/terraform apply -var-file=${env}.tfvars
    '';

  syncS3 = env:
    writeShellScript "syncs3" ''
    ${awscli}/bin/aws s3 sync --delete ${marlowe-playground.client} s3://marlowe-playground-website-${env}/
    # We do a sync to delete any files that have been removed, just to keep things clean, then we do a recursive cp
    # because sync doesn't update files with the same file size and timestamp
    ${awscli}/bin/aws s3 cp --recursive ${marlowe-playground.client} s3://marlowe-playground-website-${env}/'';

  deploy = env: region:
    writeShellScript "deploy" ''
      set -e
      tmp_dir=$(mktemp -d)
      echo "using tmp_dir $tmp_dir"

      ln -s ${./terraform}/* $tmp_dir

      # in case we have some tfvars around in ./terraform
      rm $tmp_dir/*.tfvars | true

      ln -s ${terraform-locals env}/* $tmp_dir
      ln -s ${terraform-vars env region}/* $tmp_dir
      cd $tmp_dir

      echo "apply terraform"
      export TF_VAR_marlowe_github_client_id=$(pass ${env}/marlowe/githubClientId)
      export TF_VAR_marlowe_github_client_secret=$(pass ${env}/marlowe/githubClientSecret)
      export TF_VAR_marlowe_jwt_signature=$(pass ${env}/marlowe/jwtSignature)
      ${terraform}/bin/terraform init
      ${terraform}/bin/terraform workspace select ${env}
      ${terraform}/bin/terraform apply -var-file=${env}.tfvars
      api_id=$(${terraform}/bin/terraform output rest_api_id)
      region=$(${terraform}/bin/terraform output region)

      echo "sync with S3"
      ${syncS3 env}

      echo "deploy api"
      ${awscli}/bin/aws apigateway create-deployment --region $region --rest-api-id $api_id --stage-name ${env}

      echo "done"
    '';

  mkEnv = env: region: {
    inherit terraform-vars terraform-locals terraform;
    syncS3 = (syncS3 env);
    runTerraform = (runTerraform env region);
    deploy = (deploy env region);
  };

  envs = {
    david = mkEnv "david" "eu-west-1";
    alpha = mkEnv "alpha" "eu-west-2";
  };
in envs // { inherit getCreds; }
