{ pkgs, marlowe-playground, marlowe-symbolic-lambda }:
with pkgs;
let
  # 20.03 version of terraform is broken on some versions of OSX so I have copied the last 0_12 version from nixpkgs
  terraform = (callPackage ./terraform.nix { }).terraform_0_12;

  getCreds = pkgs.writeShellScript "getcreds" ''
    export AWS_PROFILE=dev-mantis
    unset AWS_SESSION_TOKEN
    unset AWS_SECRET_ACCESS_KEY
    unset AWS_ACCESS_KEY_ID

    ${awscli}/bin/aws sts get-session-token --serial-number arn:aws:iam::454236594309:mfa/david.smith --output text --duration-seconds 86400 --token-code $1 \
            | awk '{printf("export AWS_ACCESS_KEY_ID=\"%s\"\nexport AWS_SECRET_ACCESS_KEY=\"%s\"\nexport AWS_SESSION_TOKEN=\"%s\"\n",$2,$4,$5)}'
      '';

  terraform-locals = env:
    writeTextFile {
      name = "terraform-locals";
      destination = "/generated.tf.json";
      text = (builtins.toJSON {
        locals = {
          env = "${env}";
          marlowe_client = "${marlowe-playground.client}";
        };
      });
    };

  terraform-vars = env:
    writeTextFile {
      name = "terraform-vars";
      destination = "/${env}.tfvars";
      text = if pkgs.stdenv.isDarwin then
        ""
      else
        ''
          symbolic_lambda_file="${marlowe-symbolic-lambda}/marlowe-symbolic.zip"'';
    };

  runTerraform = env:
    writeShellScript "terraform" ''
      tmp_dir=$(mktemp -d)
      ln -s ${./terraform}/* $tmp_dir
      ln -s ${terraform-locals env}/* $tmp_dir
      ln -s ${terraform-vars env}/* $tmp_dir
      cd $tmp_dir
      ${terraform}/bin/terraform init
      ${terraform}/bin/terraform workspace select ${env}
      ${terraform}/bin/terraform apply -var-file=${env}.tfvars
    '';

  syncS3 = env:
    writeShellScript "syncs3"
    "${awscli}/bin/aws s3 sync ${marlowe-playground.client} s3://marlowe-playground-website/${env}";

  deploy = env:
    writeShellScript "deploy" ''
      echo "apply terraform"
      ${runTerraform env} -auto-approve
      echo "sync with S3"
      ${syncS3 env}
      echo "done"
    '';

  mkEnv = env: {
    inherit getCreds terraform-vars terraform-locals terraform;
    syncS3 = (syncS3 env);
    runTerraform = (runTerraform env);
    deploy = (deploy env);
  };

  envs = { david = mkEnv "david"; };
in envs
