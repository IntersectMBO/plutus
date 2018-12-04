# Plutus Playground Infrastructure

The infrastructure is comprised of 2 parts:

## Terraform

We use `terraform` to manage the AWS infrastructure including networking, loadbalancing and machines.

### Creating AWS infrastructure

1. You must have an account in the plutus-playground AWS account (you will need a lot of capabilities, so an admin account is easiest)
2. Authenticate your account in the current shell session
3. Create the Route 53 zone you want to use (e.g. playground.plutus.iohkdev.io) and add an NS record in the parent zone.
3. Change all occurrences of `playground.plutus.iohkdev.io` to your zone (TODO: improve this to not duplicate)
3. Fix all hard-coded route 53 zones in the terraform config (TODO: improve this to not hard-code anything that can't be easily overridden)
3. Setup ACM for wildcard on that zone.
3. Move into the `plutus-playground/deployment/terraform` directory
4. Initialize terraform with `terraform init`
5. Optionally, if you need to manage multiple workspaces, create a new terraform workspace with `terraform workspace new myname`
6. In `variables.tf` make sure that your ssh key is in the variable `ssh_keys` under the entry `myname`. You then need to add and entry in each of the `*_ssh_keys` variables with `myname = ["myname"]`. Then key is the environment name and the value is a list of people who can have ssh access to those machines.
7. Copy `terraform.tfvars.example` to `terraform.tfvars` or a custom tfvars file if you want to pass the `var-file` on the command line.
8. Edit `myname.tfvars` or `terraform.tfvars`, changing myname and home directories etc.
9. Check what changes terraform will make with `terraform plan -var-file=myname.tfvars`
10. If you are happy with all changes run `terraform apply -var-file=myname.tfvars`
11. You should see a new file `/home/myname/.ssh/config.d/plutus_playground.conf`
12. Add the line `Include config.d/*.conf` to the top of your `/home/myname/.ssh/config` file. This will make it easier to ssh to the machines

You should now have a complete infrastructure however not much is installed on the machines. You can see the available machines and their addresses with `cat ~/.ssh/config.d/plutus_playground`. You can ssh to the machines as `root` in an emergency, but this should never ever be done unless the machine is completely unreachable from
nixops host. You should always ssh using the `nixops ssh <host>` command on nixops host instead of directly logging in as root over ssh.

## Nixops

The individual machines now exist but have nothing installed on them. We configure these machines and install services using nixops.

### Configure the machines

1. ssh onto the nixops machine `ssh -A root@nixops.plutus_playground` and accept the fingerprints
2. exit the machine and from the project root copy the generated json files onto the nixops machine `scp plutus-playground/deployment/nixops/*.json root@nixops.plutus_playground:~/plutus/plutus-playground/deployment/nixops`
3. ssh onto the nixops machine again `ssh -A root@nixops.plutus_playground`
4. Install git `nix-env -iA nixos.git`
5. Clone the plutus repository `git clone https://github.com/input-output-hk/plutus.git`
6. Enter the project `cd plutus`
7. Switch to the branch you want to work with e.g. `git checkout plutus`
8. Move into the nixops directory `cd plutus-playground/deployment/nixops/`
9. Create a new deployment `nixops create ./default.nix ./network.nix -d play`
10. Deploy the new deployment `nixops deploy -d play`
11. You should now be able to reach the playground at [https://myname.playground.plutus.iohkdev.io](https://myname.playground.plutus.iohkdev.io)

Note:

Currently there is a bug where the first time you submit some code to the playground, it will take 2 mins to evaluate. From the front end you will see a gateway timeout error. This is made even worse as we have multiple instances however there will be some workarounds soon.

## Updating an environment

1. Authenticate your account in the current shell session
2. Move into the `plutus-playground/deployment/terraform` directory
3. Check what changes terraform will make with `terraform plan -var-file=myname.tfvars`
4. If you are happy with all changes run `terraform apply -var-file=myname.tfvars`
5. From the project root copy the generated json files onto the nixops machine `scp plutus-playground/deployment/nixops/*.json root@nixops.plutus_playground:~/plutus/plutus-playground/deployment/nixops` (TODO: automate this)
6. ssh onto the nixops machine again `ssh -A root@nixops.plutus_playground`
7. update plutus with `cd plutus && git pull`
8. deploy the latest with `cd plutus-playground/deployment/nixops && nixops modify ./default.nix ./network.nix -d play && nixops deploy -d play`
