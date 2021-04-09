# Plutus/Marlowe Deployment

[shell.nix](./shell.nix) provides multiple environment-specific shells for deploying plutus/marlowe infrastructure to AWS using terraform and morph.

## Usage

There are individual shells for each configured environment. In order to enter a shell for the `alpha` environment you would enter a shell as follows:

```
$ nix-shell -A alpha
```

The shell will show an overview of available commands as shown below:

```
---------------------------------------------------------------------
deployment shell for 'tobias'
---------------------------------------------------------------------
Available commands:

        * provision-infra:  provision infrastructure
        * destroy-infra:    destroy the infrastructure completely
        * deploy-nix:       deploy nix configuration to infrastructure
        * deploy:           provision infrastructure and deploy nix configuration
Notes:

- Being logged in to aws via 'aws-mfa-login' is a prerequisite to all infrastructure commands
- The './terraform' dir has to be specified to run arbitrary terraform commands (e.g. 'terraform plan ./terraform')
- The './morph/configurations.nix' file has to be specified to run arbitrary morph commands (e.g. 'morph build ./morph/configurations.nix)
```

Instead of entering the shell for an interactive session you can also just execute a full deployment instead:

```
$ nix-shell -A alpha --command deploy
```

The deploy command will run execute `terraform` and `morph` in sequence. All other available commands can be
executed in the same way.

### AWS Login

In order to use the shell you need to be logged in with AWS. This will be verified at the start of the shell.
To log in use `aws-mfa-login` which is provided by the top-level shell.nix:

```
$ eval $(aws-mfa-login <username> <mfa-code>)
```
