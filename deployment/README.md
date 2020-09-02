# Plutus and Marlowe Playgrounds Infrastructure

## New infrastructure

We are currently in the process of migrating to a new infrastructure, at the moment this is just for the marlowe playground but the intention is to move the plutus playground soon after. The new infrastructure aims to do the following:

1. Remove the need for managing servers
2. Make setup and configuration easy by using nix to generate scripts to do everything
3. Make scaling easier and quicker
4. Cut costs

A website is served from AWS API Gateway which will proxy to the following parts:

* static data is stored in S3
* anything that can be run in a lambda is
* other things (currently web-ghc) are run elsewhere (currently on the old server infrastructure)

### Getting Started

If you are using OSX then you cannot build the lambdas locally, therefore if you want to update the infrastructure you will need to build the lambdas on a linux machine and then copy them to a location on your machine. Then you can set the env var `export TF_VAR_symbolic_lambda_file=/path/to/marlowe-symbolic.zip`.

If you have not setup AWS authentication but you have enabled MFA then you can run `$(nix-build -A deployment.david.getCreds) user.name 123456` (where 123456 is the current MFA code) before you run any other command to setup temporary credentials that are valid for 24 hours.

The scripts produce files for use with nixops (until we get rid of the legacy infra) and so you should provide the location where you want these files to go by setting another terraform variable, e.g. `export TF_VAR_nixops_root=$(pwd)/deployment/nixops`.

The infrastructure is based around multiple environments, for example `alpha`, `david` etc. Scripts exist for updating a particular environment under the `deployment` attribute, e.g. the main deployment script for the environment `david` can be run with `$(nix-build -A deployment.david.deploy)`. This will run other scripts that will do everything needed. These other scripts can be run individually, which can be useful if you are playing around with the infrastructure.

* `deployment.env.runTerraform` will run only the terraform apply command
* `deployment.env.syncS3` will sync the marlowe client static code with S3
* `deployment.env.terraform-locals` will produce `generated.tf.json` which contains locals such as `env`
* `deployment.env.terraform-vars` will produce `env.tfvars` which contains variables such as `symbolic_lambda_file` if you are not on OSX

## Legacy Infrastructure

The legacy infrastructure is comprised of 2 parts, terraform and nixops:

## Terraform

We use `terraform` to manage the AWS infrastructure including networking, loadbalancing and machines.

### Creating AWS infrastructure

1. You must have an account in the plutus-playground or dev-mantis AWS account (you will need a lot of capabilities, so an admin account is easiest)
2. Authenticate your account in the current shell session
3. Create the Route 53 zone you want to use (e.g. playground.plutus.iohkdev.io) and add an NS record in the parent zone.
4. Setup ACM for wildcard on that zone.
5. Move into the `deployment/terraform` directory
6. Initialize terraform with `terraform init`
7. Optionally, if you need to manage multiple workspaces, create a new terraform workspace with `terraform workspace new myname`
8. In `variables.tf` make sure that your ssh key is in the variable `ssh_keys` under the entry `myname`. You then need to add and entry in each of the `*_ssh_keys` variables with `myname = ["myname"]`. Then key is the environment name and the value is a list of people who can have ssh access to those machines.
9. Copy `terraform.tfvars.example` to `terraform.tfvars` or a custom tfvars file if you want to pass the `var-file` on the command line.
10. Edit `myname.tfvars` or `terraform.tfvars`, changing myname and home directories etc.
11. Set tld in `tfvars` file to your zone
12. Check what changes terraform will make with `terraform plan -var-file=myname.tfvars`
13. If you are happy with all changes run `terraform apply -var-file=myname.tfvars`
14. You should see a new file `/home/myname/.ssh/config.d/plutus_playground.conf`
15. Add the line `Include config.d/*.conf` to the top of your `/home/myname/.ssh/config` file. This will make it easier to ssh to the machines

You should now have a complete infrastructure however not much is installed on the machines. You can see the available machines and their addresses with `cat ~/.ssh/config.d/plutus_playground`. You can ssh to the machines as `root` in an emergency, but this should never ever be done unless the machine is completely unreachable from
nixops host. You should always ssh using the `nixops ssh <host>` command on nixops host instead of directly logging in as root over ssh.

The key for API Gateway (`apiGatewayKey` in the `secrets.json` file mentioned in next section) can be found in the AWS console in the API Gateway section, API Keys (left menu), then select the API Key in the list, and then click the `Show` hyperlink in the `API key` field on the right hand side.

It seems currently the API Gateway end-point is not deployed automatically. It can also be deployed from the console by going to API Gateway, click in the API to deploy, and in the resources section resources click actions, and then Deploy API in the drop down menu ([related stack overflow question](https://stackoverflow.com/questions/38910937/terraform-not-deploying-api-gateway-stage)).

## Nixops

The individual machines now exist but have nothing installed on them. We configure these machines and install services using nixops.

### Configure the machines

1. ssh onto the nixops machine `ssh nixops.plutus_playground` and accept the fingerprints
2. Clone the plutus repository `git clone https://github.com/input-output-hk/plutus.git`
3. exit the machine and from the project root copy the generated json files onto the nixops machine `scp ./deployment/nixops/*.json root@nixops.plutus_playground:~/plutus/deployment/nixops`
4. ssh onto the nixops machine again `ssh -A nixops.plutus_playground` (notice `-A` you will need agent forwarding)
5. Enter the project `cd plutus`
6. Switch to the branch you want to work with e.g. `git checkout master`
7. Move into the nixops directory `cd deployment/nixops/`
8. Create a file called `secrets.json` that is based on [the example file](./nixops/secrets.json.example).
9. Create a new deployment `nixops create ./default.nix ./network.nix -d playgrounds`
10. Deploy the new deployment `nixops deploy`
11. You should now be able to reach the plutus playground at [https://myname.plutus.iohkdev.io] (https://myname.plutus.iohkdev.io) and marlowe playground at [https://myname.marlowe.iohkdev.io] (https://myname.marlowe.iohkdev.io)

## Updating an environment

Most of the time, an environment can be updated without touching terraform at all.

1. ssh onto the nixops machine again `ssh -A nixops.plutus_playground`
2. update plutus with `cd plutus && git pull`
3. deploy the latest with `nixops deploy`

In the case that terraform code is altered in a way that re-created the nixops machine, you will need to go through the entire `Configure the machines` section above. If the nixops machine is not altered, you will be able to copy `machine.json` and just `nixops deploy` after applying terraform code.

WARNING: altering some ssh keys in terraform instances can result in machines being recreated. Ensure with others using machines that it's okay to bring down everything before running any terraform commands. Also a close inspection of `terraform plan` can help assess the danger of running `terraform apply`. Usually you don't want to change these keys anyway as user keys are managed by nixops. As an example, changing `var.nixops_ssh_keys` will result in the nixops machine being re-created however changing `var.playground_ssh_keys` will only change the `machines.json` file that nixops uses.

## Deployment Server

If you wish to use the continuous delivery deployment server then please read the [Readme](../deployment-server/README.md).

## Changing User Data

Sometimes it is necessary to change the `user_data` field in an EC2 machine, for example if you want to upgrade nixpkgs on the machine definition in `deployment.nixos` then you should ensure `user_data` is also changed. This ensures that if the machine is ever re-created (or when a new environment is created) the correct initial nixos configuration is used.

When `user_data` is modified, terraform will see there is a difference and ask to re-create the machine, this is often undesirable and you can work around it as follows:

* add something like the following to the bottom of `main.tf` where the correct `user_data` is used:

```terraform
output "user_data" {
  value = "${data.template_file.nixops_user_data.rendered}"
}
```

* run `terraform refresh -var-file=myvars.tf`
* go to the AWS console -> EC2 -> instances and find the instance(s) with the user data you want to change
* stop the machine
* change the user data (Instance Settings -> View/Change User Data)
* start the machine
* run `terraform apply -var-file=myvars.tf`

If terraform still thinks it needs to make a change to `user_data` it's probably because there is a missing or extra newline in the user data. You can fiddle with this by putting the user data in a file and adjust and run `cat userdata | shasum` until you get the same sha that terraform is expecting.

Finally you should delete the `output` you created in `main.tf` as it creates noise in the output.