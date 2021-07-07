{ lib, config, pkgs, ... }:
let
  inherit (builtins) foldl';
  inherit (pkgs.terralib) sops2kms sops2region cidrsOf;
  inherit (lib) splitString forEach unique flatten;
  inherit (config) cluster;
  inherit (cluster) s3Bucket kms;
  bucketArn = "arn:aws:s3:::${s3Bucket}";
in {
  cluster.iam = {
    roles = let
      # "a/b/c/d" => [ "" "/a" "/a/b" "/a/b/c" "/a/b/c/d" ]
      pathPrefix = rootDir: dir:
        let
          fullPath = "${rootDir}/${dir}";
          splitPath = splitString "/" fullPath;
          cascade = foldl' (s: v:
            let p = "${s.path}${v}/";
            in {
              acc = s.acc ++ [ p ];
              path = p;
            }) {
              acc = [ "" ];
              path = "";
            } splitPath;

        in cascade.acc;
      allowS3For = prefix: rootDir: bucketDirs: {
        "${prefix}-s3-bucket-console" = {
          effect = "Allow";
          actions = [ "s3:ListAllMyBuckets" "s3:GetBucketLocation" ];
          resources = [ "arn:aws:s3:::*" ];
        };

        "${prefix}-s3-bucket-listing" = {
          effect = "Allow";
          actions = [ "s3:ListBucket" ];
          resources = [ bucketArn ];
          condition = forEach bucketDirs (dir: {
            test = "StringLike";
            variable = "s3:prefix";
            values = pathPrefix rootDir dir;
          });
        };

        "${prefix}-s3-directory-actions" = {
          effect = "Allow";
          actions = [ "s3:*" ];
          resources = unique (flatten (forEach bucketDirs (dir: [
            "${bucketArn}/${rootDir}/${dir}/*"
            "${bucketArn}/${rootDir}/${dir}"
          ])));
        };
      };
    in {
      client = {
        assumePolicy = {
          effect = "Allow";
          action = "sts:AssumeRole";
          principal.service = "ec2.amazonaws.com";
        };

        policies = let
          s3Secrets =
            allowS3For "secrets" "infra/secrets/${cluster.name}/${kms}" [
              "client"
              "source"
            ];
          s3Cache = allowS3For "cache" "infra" [ "binary-cache" ];
        in s3Secrets // s3Cache // {
          ssm = {
            effect = "Allow";
            resources = [ "*" ];
            actions = [
              "ec2:ReportInstanceStatus"
              "ec2messages:AcknowledgeMessage"
              "ec2messages:DeleteMessage"
              "ec2messages:FailMessage"
              "ec2messages:GetEndpoint"
              "ec2messages:GetMessages"
              "ec2messages:SendReply"
              "ssmmessages:CreateControlChannel"
              "ssmmessages:CreateDataChannel"
              "ssmmessages:OpenControlChannel"
              "ssmmessages:OpenDataChannel"
              "ssm:DescribeAssociation"
              "ssm:GetDeployablePatchSnapshotForInstance"
              "ssm:GetDocument"
              "ssm:DescribeDocument"
              "ssm:GetManifest"
              "ssm:GetParameter"
              "ssm:GetParameters"
              "ssm:ListAssociations"
              "ssm:ListInstanceAssociations"
              "ssm:PutInventory"
              "ssm:PutComplianceItems"
              "ssm:PutConfigurePackageResult"
              "ssm:UpdateAssociationStatus"
              "ssm:UpdateInstanceAssociationStatus"
              "ssm:UpdateInstanceInformation"
            ];
          };

          ecr = {
            effect = "Allow";
            resources = [ "*" ];
            actions = [
              "ecr:GetAuthorizationToken"
              "ecr:BatchCheckLayerAvailability"
              "ecr:GetDownloadUrlForLayer"
              "ecr:GetRepositoryPolicy"
              "ecr:DescribeRepositories"
              "ecr:ListImages"
              "ecr:DescribeImages"
              "ecr:BatchGetImage"
              "ecr:GetLifecyclePolicy"
              "ecr:GetLifecyclePolicyPreview"
              "ecr:ListTagsForResource"
              "ecr:DescribeImageScanFindings"
            ];
          };

          nomad = {
            effect = "Allow";
            resources = [ "*" ];
            actions = [ "autoscaling:SetInstanceHealth" ];
          };

          consul = {
            effect = "Allow";
            resources = [ "*" ];
            actions = [
              "ec2:DescribeInstances"
              "ec2:DescribeTags"
              "autoscaling:DescribeAutoScalingGroups"
            ];
          };

          vault = {
            effect = "Allow";
            resources = [ "*" ];
            actions = [
              "ec2:DescribeInstances"
              "iam:GetInstanceProfile"
              "iam:GetUser"
              "iam:GetRole"
              "logs:CreateLogStream"
              "logs:PutLogEvents"
            ];
          };

          kms = {
            effect = "Allow";
            resources = [ kms ];
            actions = [ "kms:Encrypt" "kms:Decrypt" "kms:DescribeKey" ];
          };
        };
      };

      core = {
        assumePolicy = {
          effect = "Allow";
          action = "sts:AssumeRole";
          principal.service = "ec2.amazonaws.com";
        };

        policies = let
          s3Secrets =
            allowS3For "secret" "infra/secrets/${cluster.name}/${kms}" [
              "server"
              "client"
              "source"
            ];
          s3Cache = allowS3For "cache" "infra" [ "binary-cache" ];
        in s3Secrets // s3Cache // {
          kms = {
            effect = "Allow";
            resources = [ kms ];
            actions = [ "kms:Encrypt" "kms:Decrypt" "kms:DescribeKey" ];
          };

          change-route53 = {
            effect = "Allow";
            resources =
              [ "arn:aws:route53:::hostedzone/*" "arn:aws:route53:::change/*" ];
            actions = [
              "route53:GetChange"
              "route53:ChangeResourceRecordSets"
              "route53:ListResourceRecordSets"
            ];
          };

          list-route53 = {
            effect = "Allow";
            actions = [ "route53:ListHostedZonesByName" ];
            resources = [ "*" ];
          };

          assumeRole = {
            effect = "Allow";
            resources = [
              cluster.instances.core-1.iam.instanceProfile.tfArn
              cluster.instances.core-2.iam.instanceProfile.tfArn
              cluster.instances.core-3.iam.instanceProfile.tfArn
            ];
            actions = [ "sts:AssumeRole" ];
          };

          ssm = {
            effect = "Allow";
            resources = [ "*" ];
            actions = [
              "ec2:ReportInstanceStatus"
              "ec2messages:AcknowledgeMessage"
              "ec2messages:DeleteMessage"
              "ec2messages:FailMessage"
              "ec2messages:GetEndpoint"
              "ec2messages:GetMessages"
              "ec2messages:SendReply"
              "ssmmessages:CreateControlChannel"
              "ssmmessages:CreateDataChannel"
              "ssmmessages:OpenControlChannel"
              "ssmmessages:OpenDataChannel"
              "ssm:DescribeAssociation"
              "ssm:GetDeployablePatchSnapshotForInstance"
              "ssm:GetDocument"
              "ssm:DescribeDocument"
              "ssm:GetManifest"
              "ssm:GetParameter"
              "ssm:GetParameters"
              "ssm:ListAssociations"
              "ssm:ListInstanceAssociations"
              "ssm:PutInventory"
              "ssm:PutComplianceItems"
              "ssm:PutConfigurePackageResult"
              "ssm:UpdateAssociationStatus"
              "ssm:UpdateInstanceAssociationStatus"
              "ssm:UpdateInstanceInformation"
            ];
          };

          nomad = {
            effect = "Allow";
            resources = [ "*" ];
            actions = [ "autoscaling:SetInstanceHealth" ];
          };

          consul = {
            effect = "Allow";
            resources = [ "*" ];
            actions = [
              "ec2:DescribeInstances"
              "ec2:DescribeTags"
              "autoscaling:DescribeAutoScalingGroups"
            ];
          };

          vault = {
            effect = "Allow";
            resources = [ "*" ];
            actions = [
              "ec2:DescribeInstances"
              "iam:AddUserToGroup"
              "iam:AttachUserPolicy"
              "iam:CreateAccessKey"
              "iam:CreateUser"
              "iam:DeleteAccessKey"
              "iam:DeleteUser"
              "iam:DeleteUserPolicy"
              "iam:DetachUserPolicy"
              "iam:GetInstanceProfile"
              "iam:GetRole"
              "iam:GetUser"
              "iam:ListAccessKeys"
              "iam:ListAttachedUserPolicies"
              "iam:ListGroupsForUser"
              "iam:ListUserPolicies"
              "iam:PutUserPolicy"
              "iam:RemoveUserFromGroup"
              "logs:CreateLogStream"
              "logs:PutLogEvents"
              # TODO: "Resource": ["arn:aws:iam::ACCOUNT-ID-WITHOUT-HYPHENS:user/vault-*"]
            ];
          };
        };
      };
    };
  };
}
