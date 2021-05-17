# Plutus/Marlowe Deployment

<img align="left" src="https://badge.buildkite.com/d1e532e610e22c0e918b69938be8a644f615c9920e3d17cdaf.svg?branch=master"> staging environment deployment

<img align="left" src="https://badge.buildkite.com/d1e532e610e22c0e918b69938be8a644f615c9920e3d17cdaf.svg?branch=production"> production environment deployment

## Overview

The deployment uses a combination of [Terraform](https://www.terraform.io/) and [Morph](https://github.com/DBCDK/morph) where Terraform creates the instances and network configuration on AWS and Morph deploys and activates the NixOS configurations.

- [terraform configuration files](https://github.com/input-output-hk/plutus/tree/master/deployment/terraform)
- [morph deployment files](https://github.com/input-output-hk/plutus/tree/master/deployment/morph)
- [NixOS modules](https://github.com/input-output-hk/plutus/tree/master/nix/modules)

### Continuous Delivery

The [server configurations](https://github.com/input-output-hk/plutus/tree/master/deployment/morph/default.nix) that will be deployed via morph are built by hydra and are deployed by buildkite pipelines (see [pipeline.yml](https://github.com/input-output-hk/plutus/blob/master/.buildkite/pipeline.yml)). Two pipelines are set up for this purpose:

- **master**: Successful [master branch builds](https://hydra.iohk.io/jobset/Cardano/plutus) are automatically deployed to the staging environment via the [_master_ pipeline](https://buildkite.com/input-output-hk/plutus/builds?branch=master)
- **production**: Production deployments are triggered by the [_production_ deployment pipeline on buildkite](https://buildkite.com/input-output-hk/plutus/builds?branch=master) whenever the `production` branch changes.

### Environments

There are several environments to deploy to. All available environments are listed in [deployment/envs.nix](https://github.com/input-output-hk/plutus/tree/master/deployment/envs.nix):

```nix
# deployment/envs.nix (excerpt)
{
  alpha = { region = "eu-west-2"; };
  production = { region = "eu-west-1"; };
}
```

Environments are deployed to `<env>.iohkdev.io`.

#### Deployment Versions
`alpha` is the staging environment to which the `master` branch is deployed automatically. The `production` environment is reserved for the live environment. Additional environments are available for testing purposes.

Ideally the `alpha` deployment should always reflect the current state of `master`, and `production` should always reflect the current state of the `production` branch. This can be verified using the `/version` endpoint:

```shell
$ curl https://alpha.plutus.iohkdev.io/version
{"rev": "13342f6981faabdc2bb7e88a9cb5a3990f7a4930"}

$ curl https://production.plutus.iohkdev.io/version
{"rev": "acc7a4486d50844690fb485b74abab44908bd39b"}
```

## Usage

**NOTE**: Deployments to either the `staging` or the `production` environment **should never** be done manually unless there is a _good reason_ to do so. Instead, the buildkite pipelines should be used for this.

#### Prerequisites
- AWS account
- Active plutus nix-shell environment

In order to to deploy anything you need to log in to your AWS account:
```shell
$ eval $(aws-mfa-login <username> <mfa-code>)
```
The deployment scripts will validate the login status and abort if no valid session can be found.

#### Commands

The following deployment commands are made available through a nix-shell:

- **provision-infra** provisions the infrastructure on AWS using terraform.
- **destroy-infra** deletes previously provisioned infrastructure on AWS using terraform.
- **deploy-nix** deploys nixos configurations to Terraform provisioned servers using morph.
- **deploy** runs both, `provision-infra` followed by `deploy-nix`.

##### provision-infra

```shell
$ nix-shell -A <env> --run "provision-infra"
```
- The `provision-infra` command executes `terraform apply` updating AWS to be in sync with the current state of configuration.
- Running `provision-infra` may destroy and/or create several, all, or no resources at all. Execution times will differ respectively.

##### destroy-infra

```shell
$ nix-shell -A <env> --run "destroy-infra"
```
- The `destroy-infra` command executes `terraform destroy` and destroys all resources previously created by terraform.

##### deploy-nix

```shell
$ nix-shell -A <env> [--argstr rev <git commit>] --run "deploy-nix"
```
- The deploy-nix command executes `morph deploy` to copy and activate the most recent nix packages
- If the environment infrastructure is not up to date (meaning `terraform apply` would not be a no-op) the deployment will abort.

##### deploy

```shell
$ nix-shell -A <env> [--argstr rev <git commit>] --run "deploy"
```
- The deploy command combines `provision-infra` and `deploy-nix`: It performs `terraform apply` followed by `morph deploy`.
- The `rev` argument is optional and defaults to `dev` when not specified. The value of `rev` is returned by the `/version` endpoint as explained above.


## Secrets

The deployment depends on several credentials which are maintained using the [AWS Secrets Manager](https://aws.amazon.com/secrets-manager/). The secrets are organized per environment with the following structure:

```json
{
  "env": "<name of the environment>",
  "marlowe": {
    "githubClientId": "<id>",
    "githubClientSecret": "<secret>",
    "jwtSignature": "<jwt-token>"
  },
  "plutus": {
    "githubClientId": "<id>",
    "githubClientSecret": "<secret>",
    "jwtSignature": "<jwt-token>"
  }
}
```

The deployment scripts will obtain this json document for the respective environment and expose them to terraform through several
environment variables.


## Maintenance

The sections below describe actions relevant for advanced usage or maintenance of the deployment process.

### Adding Users
Adding new users that are able to perform deployments requires 2 individual steps:

1. Creating an AWS account for the new user
2. Adding the user's ssh key

The AWS login is required in order to provision infrastructure using Terraform. The ssh key has to be added in order to enable users to perform deployments with morph through the ssh jump host.

#### AWS
The new user has to be added to the appropriate AWS organization. Please talk to a plutus/marlowe team member and request access. New
users with appropriate permissions have to be added manually through the aws console.

#### Terraform
In order to perform nix deployments a ssh-key has to be configured in [deployment/terraform/locals.tf](https://github.com/input-output-hk/plutus/blob/master/deployment/terraform/locals.tf):

**1.** **Create a new ssh keypair**:

```
$ ssh-keygen -t ed25519
```

**2.** **Add the user/key to the `ssh_keys` map in** [deployment/terraform/locals.tf](https://github.com/input-output-hk/plutus/blob/master/deployment/terraform/locals.tf)

```

ssh_keys = {
    username = "ssh-ed25519 AAAAC...f3JfmL3A2 usernamer@host
}
```

**3**. **Add the new user to environments that they should be able to deploy to**

In order to allow the user (ssh key) to deploy to the `testing` environment [deployment/terraform/locals.tf](https://github.com/input-output-hk/plutus/blob/master/deployment/terraform/locals.tf) needs to be edited as shown below:

```
  bastion_ssh_keys_ks = {
    testing = ["username"]
    ...
  }

  root_ssh_keys_ks = {
    testing = ["username"]
    ..
  }
```

### Adding Environments

Deployments can be performed to different environments. Each environment is a full aws setup with multiple ec2 instances and networking, deployed to different `iohkdev.io` subdomains:

- The `alpha` environment is deployed to `alpha.iohkdev.io`
- `testing` is deployed to `testing.iohkdev.io`

Terraform uses different workspaces for each environment which are also separated in the shared state which is stored in a S3 bucket. When entering a nix-shell the respective terraform workspace is chosen automatically.

In order to add a new environment the following steps need to be followed:

**1. Add the environment to [deployment/envs.nix](https://github.com/input-output-hk/plutus/blob/master/deployment/envs.nix)**

In order to add an environment `environment` it needs to be added to the attribute set in `deployment/envs.nix` as follows:

```nix
{
    environment = { region = "eu-west-3"; };
}
```

**2. Add users that can deploy to the environment**:

Make sure that users that should be able to deploy to the new environment are added to it in [deployment/terraform/locals.tf](https://github.com/input-output-hk/plutus/blob/master/deployment/terraform/locals.tf) as described above in section about adding users.


**3. Configure credentials for the environment**:

In order for the deployment to work it requires access to the secrets described above in the **Secrets** section. The secrets are obtained from the _AWS Secrets Manager_ but they need to be imported first for every environment:

First create a json file containing the necessary credentials in the `deployment` directory:
```json
{
  "env": "<name of the environment>",
  "marlowe": {
    "githubClientId": "<id>",
    "githubClientSecret": "<secret>",
    "jwtSignature": "<jwt-token>"
  },
  "plutus": {
    "githubClientId": "<id>",
    "githubClientSecret": "<secret>",
    "jwtSignature": "<jwt-token>"
  }
}
```
Then use `aws-upload-secrets` to submit it:

```shell
$ nix-shell aws-upload-secrets.nix --argstr env <name> --run "aws-upload-secrets ./file.json"
```

You should now be able to acess the nix-shell for the newly created environment in which the credentials you just uploaded should be set in several environment variables:

```shell
$ nix-shell -A <name>
$ echo $TF_VAR_plutus_github_client_id # should print the value you just configured
```


### Extending The Deployment

The deployment process is split between provisioning the infrastructure on AWS using Terraform and deploying NixOS configurations with updated packages or service descriptions using morph. Depending on the respective changes, either one or both of these layers have to be updated.

#### Adding Servers
The currently configured ec2 instances are easy to discover:

- morph: [deployment/morph/machines.nix](https://github.com/input-output-hk/plutus/blob/master/deployment/morph/machines.nix)
- Terraform: [deployment/terraform/machines.tf](https://github.com/input-output-hk/plutus/blob/master/deployment/terraform/machines.tf)

The terraform file represents a local resource which is consumed by the morph configuration to obtain information that only terraform can provide. Both files represent the respective entry point to configuring a new server. On the Terraform side the ec2 instance hardware, network and SSL certificates have to be configured. On the morph side there has to be a NixOS configuration describing the software setup.


#### Adding Services
Assuming you only want to add a service to an existing server, you can follow these steps:

- Expose relevant packages in [default.nix](https://github.com/input-output-hk/plutus/blob/master/default.nix)
- Create a NixOS module describing your service in [nix/modules](https://github.com/input-output-hk/plutus/tree/master/nix/modules)


#### Configuring A New Domain
Configuring a newly purchased domain for use with a deployment environment requires several changes, most of them to the Terraform code:
1. **Hosted Zone Configuration**: Add a new hosted zone in the route53 configuration on the aws console
1. **Update NS Entries**: Configure the new domain (externally) to use the name servers of the hosted zone
1. **ALB Configuration**: Configure the routing for the new domain in [loadbalancing.tf](https://github.com/input-output-hk/plutus/blob/master/deployment/terraform/loadbalancing.tf)
1. **Configure Certificates**: Configure certificates for the new domain in [certificates.tf](https://github.com/input-output-hk/plutus/blob/master/deployment/terraform/certificates.tf)

The changes in [this PR](https://github.com/input-output-hk/plutus/pull/3107) can be used as reference.
