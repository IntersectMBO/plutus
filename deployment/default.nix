{ pkgs, marlowe-playground, plutus-playground, marlowe-symbolic-lambda, marlowe-playground-lambda, plutus-playground-lambda }:
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
        symbolic_lambda_file="${marlowe-symbolic-lambda}/marlowe-symbolic.zip"
        playground_lambda_file="${marlowe-playground-lambda}/marlowe-playground-lambda.zip"
        plutus_playground_lambda_file="${plutus-playground-lambda}/plutus-playground-lambda.zip"'';
    };

  syncS3 = env:
    writeShellScript "syncs3" ''
      echo "sync with S3"
      ${awscli}/bin/aws s3 cp --recursive ${plutus-playground.client} s3://plutus-playground-website-${env}/
      ${awscli}/bin/aws s3 cp --recursive ${marlowe-playground.client} s3://marlowe-playground-website-${env}/
      ${awscli}/bin/aws s3 cp --recursive ${marlowe-playground.tutorial} s3://marlowe-playground-website-${env}/tutorial
      '';
  
  syncPlutusTutorial = env:
    writeShellScript "syncPlutusTutorial" ''
      echo "sync plutus tutorial with S3"
      ${awscli}/bin/aws s3 sync --delete ${plutus-playground.tutorial} s3://plutus-playground-website-${env}/tutorial
      ${awscli}/bin/aws s3 cp --recursive ${plutus-playground.tutorial} s3://plutus-playground-website-${env}/tutorial
      '';

  applyTerraform = env: region:
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
      export TF_VAR_plutus_github_client_id=$(pass ${env}/plutus/githubClientId)
      export TF_VAR_plutus_github_client_secret=$(pass ${env}/plutus/githubClientSecret)
      export TF_VAR_plutus_jwt_signature=$(pass ${env}/plutus/jwtSignature)
      ${terraform}/bin/terraform init
      ${terraform}/bin/terraform workspace select ${env}
      ${terraform}/bin/terraform apply -var-file=${env}.tfvars
      marlowe_api_id=$(${terraform}/bin/terraform output marlowe_rest_api_id)
      plutus_api_id=$(${terraform}/bin/terraform output plutus_rest_api_id)
      region=$(${terraform}/bin/terraform output region)

      echo "deploy api"
      ${awscli}/bin/aws apigateway create-deployment --region $region --rest-api-id $marlowe_api_id --stage-name ${env}
      ${awscli}/bin/aws apigateway create-deployment --region $region --rest-api-id $plutus_api_id --stage-name ${env}
    '';

  deploy = env: region:
    writeShellScript "deploy" ''
      set -e
      ${applyTerraform env region}
      ${syncS3 env}
      ${syncPlutusTutorial env}
      echo "done"
      '';

  destroy = env: region:
    writeShellScript "destroy" ''
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
      export TF_VAR_plutus_github_client_id=$(pass ${env}/plutus/githubClientId)
      export TF_VAR_plutus_github_client_secret=$(pass ${env}/plutus/githubClientSecret)
      export TF_VAR_plutus_jwt_signature=$(pass ${env}/plutus/jwtSignature)
      ${terraform}/bin/terraform init
      ${terraform}/bin/terraform workspace select ${env}
      ${terraform}/bin/terraform destroy -var-file=${env}.tfvars 
    '';

  mkEnv = env: region: {
    inherit terraform-vars terraform-locals terraform;
    syncS3 = (syncS3 env);
    syncPlutusTutorial = (syncPlutusTutorial env);
    applyTerraform = (applyTerraform env region);
    deploy = (deploy env region);
    destroy = (destroy env region);
  };

  envs = {
    david = mkEnv "david" "eu-west-1";
    kris = mkEnv "kris" "eu-west-1";
    alpha = mkEnv "alpha" "eu-west-2";
    pablo = mkEnv "pablo" "eu-west-3";
    wyohack = mkEnv "wyohack" "us-west-2";
  };
in envs // { inherit getCreds; }
