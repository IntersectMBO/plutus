# Plutus and Marlowe Playgrounds Infrastructure

Plutus and Marlowe have various web applications, currently that is:
* Plutus Playground
* Marlowe Playground
* Marlowe Dashboard

These are run on NixOS machines in AWS and in addition connect to some AWS Lambdas with some static content served from AWS S3 buckets. Deployment to this infrastructure is therefore done in 2 parts:
1. Deploying the infrastructure, lambdas and S3 content using terraform
2. Deploying the machine configuration using morph

Any machine (including OSX) can be used for deployment as long as it has the following:
* AWS admin credentials for the AWS account we use
* nix installed and working
* gpg installed and working
* if you are not on Linux then access to a Linux remote builder for nix

## Getting Started

### Remote Builder for OSX
If you are using OSX then you cannot build the lambdas and NixOS machines, therefore if you want to update the infrastructure you will need to build the lambdas on a remote builder with system type "x86_64-linux". You can do this by adding such a build machine to your `/etc/nix/machines` file, nix will try to use this machine to build the lambdas and NixOS closures.

### Secrets
We use `pass` to store secrets in the repository, given this you will need to setup your gpg key.
1. Add your key to ./deployment/keys/my.name.gpg
2. Add your name, key filename and key id to the ./deployment/default.nix `keys` attribute set
3. Run `$(nix-build -A deployment.importKeys)` to make sure you have everyone else's keys
4. Add your key name to any environment you want to be able to deploy in ./deployment/default.nix `envs`
4. Once you've added your key you will need to get someone else who already has access to enable you. To do this commit your changes to a branch and ask this person to checkout the branch, run `$(nix-build -A deployment.the_env_you_want.initPass)` and commit the changes this will have made.

### Multi-Factor Authentication (MFA)

If you have not setup AWS authentication but you have enabled MFA then you can run `eval $(getcreds <user.name> 123456)` (where 123456 is the current MFA code) before you run any other command to setup temporary credentials that are valid for 24 hours. Notice that you use `$()` to evaluate the result of the shell script and then you use `eval` on that result to evaluate the output of the script (this sets some environmental variables).


#### YubiKey

Yubikeys don't work seamlessly with `awscli`, but they do work. To set them up:

##### Setup

1. Log into the the AWS console and navigate to the "My Security Credentials" page.
2. Add your Yubikey as a "Virtual MFA device".

    _Note: AWS offers special support for U2F security keys like Yubikeys. Don't choose that option. It works for the web login, won't work with `awscli`. If you already added your Yubikey as a "U2F security key", remove it and start again._

3. The webpage will prompt you for a QR code. Instead, click the "Show secret key" link below that prompt.
4. Copy that secret key, and from your command line call:

    ```sh
    ykman oath add -t <LABEL> <SECRET_KEY>
    ```

    (`ykman` is provided by the Plutus `shell.nix`, so it should already be available on the command line.)

You're now set up to use your Yubikey as passcode-generation device for `awscli`.

For more details [see this guide](https://scalesec.com/blog/why-your-yubikey-wont-work-with-aws-cli/).

##### In Use

To generate a code, insert your Yubikey and type:

```sh
ykman oath code <LABEL>
```

It will prompt you to tap the key, and then print a One Time Passcode (OPT). You then use that code (as detailed above) with:

``` sh
eval $(getcreds <user.name> <CODE>)
```

### Environments
The infrastructure is based around multiple environments, for example `alpha`, `david` etc. Scripts exist for updating a particular environment under the `deployment` attribute, e.g. the main deployment script for the environment `david` can be run with `$(nix-build -A deployment.david.deploy)`. This will run other scripts that will do everything needed. These other scripts can be run individually, which can be useful if you are playing around with the infrastructure.

* `deployment.env.applyTerraform` will run only the terraform apply command
* `deployment.env.syncS3` will sync the marlowe client, marlowe tutorial and plutus client static code with S3
* `deployment.env.syncPlutusTutorial` will sync the plutus tutorial static code with S3, this is separate as it is 170Mb and so can take a long time
* `deployment.env.terraform-locals` will produce `generated.tf.json` which contains locals such as `env`
* `deployment.env.terraform-vars` will produce `env.tfvars` which contains variables such as `symbolic_lambda_file` if you are not on OSX

Once you have setup an environment with `$(nix-build -A deployment.david.deploy)` you will probably want to stick to using `$(nix-build -A deployment.david.applyTerraform)` and `$(nix-build -A deployment.david.syncS3)` only, avoiding dealing with the large plutus tutorial.

### SSH configuration
Running the terraform scripts will place an ssh config file in your ~/.ssh/config.d directory. This will give you easy ssh access to the servers by setting the jump hosts, usernames, dns names etc but in order for it to work you must include it in your main ssh config. Open or create the file ~/.ssh/config and add the following line at the top `Include config.d/plutus_playground.conf`. You can then test the config by running `ssh nixops.plutus_playground` which should open an ssh on the nixops machine (TODO: rename nixops machine).

This configuration is also vital for Morph to work as it assumes this ssh config so you must get this working before carrying on.

### Morph - Deploying Server Configuration
Once you have run the terraform scripts you will have an up-to-date environment with EC2 instances running, however these instances won't have the required NixOS configuration yet. In order to configure them we use morph, there is just one command for normal use: `morph deploy ./deployment/morph/default.nix switch`.

It is important to note that this is somewhat stateful in that you must run the terraform scripts beforehand to make sure that both the ssh configuration and the machine definitions (machines.json generated by terraform) are correct. Otherwise morph could try to deploy to incorrect EC2 instances.

## Changing User Data

Sometimes it is necessary to change the `user_data` field in an EC2 machine, for example if you want to upgrade nixpkgs on the machine definition in then you should ensure `user_data` is also changed. This ensures that if the machine is ever re-created (or when a new environment is created) the correct initial nixos configuration is used.

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

## Setting Up An Aws Region For First Use

TODO: I am trying to get rid of most of this section in a future PR

1. Go to the [AWS Certificate Manager](https://eu-west-2.console.aws.amazon.com/acm/home) and make sure you select the region which you wish to add certificates to.
2. If there are no certificates then click on provision a new certificate, otherwise request a certificate. Start the wizard and Request a public certificate.
3. The domain name should be `*.marlowe.iohkdev.io`.
4. Select DNS validation.
5. No tags needed.
6. Review your choices and click on Confirm and Request.
7. Now you need to setup DNS validation. On the Validation screen, expand the `*.marlowe.iohkdev.io` domain and click on Create record in Route 53. You can then Continue and after a few seconds or minutes your certificate should have status “Issued”.
8. Repeat for the other 2 domains, `*.plutus.iohkdev.io` and `*.goguen.monitoring.iohkdev.io`.
