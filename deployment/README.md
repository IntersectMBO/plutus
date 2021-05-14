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
