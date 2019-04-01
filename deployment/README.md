# Plutus Playground and Meadow Infrastructure

The infrastructure is comprised of 2 parts, terraform and nixops:

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
8. Create a file called `secrets.json` that is based on [the example file](./nixops/secrets.json.example)
9. Create a new deployment `nixops create ./default.nix ./network.nix -d plutus-playground`
10. Deploy the new deployment `nixops deploy`
11. You should now be able to reach the playground at [https://myname.plutus.iohkdev.io] (https://myname.plutus.iohkdev.io) and meadow at [https://myname.marlowe.iohkdev.io] (https://myname.marlowe.iohkdev.io)

## Updating an environment

Most of the time, an environment can be updated without touching terraform at all.

1. ssh onto the nixops machine again `ssh -A nixops.plutus_playground`
2. update plutus with `cd plutus && git pull`
3. deploy the latest with `nixops deploy`

In the case that terraform code is altered in a way that re-created the nixops machine, you will need to go through the entire `Configure the machines` section above. If the nixops machine is not altered, you will be able to copy `machine.json` and just `nixops deploy` after applying terraform code.

WARNING: altering some ssh keys in terraform instances can result in machines being recreated. Ensure with others using machines that it's okay to bring down everything before running any terraform commands. Also a close inspection of `terraform plan` can help assess the danger of running `terraform apply`. Usually you don't want to change these keys anyway as user keys are managed by nixops. As an example, changing `var.nixops_ssh_keys` will result in the nixops machine being re-created however changing `var.playground_ssh_keys` will only change the `machines.json` file that nixops uses.
