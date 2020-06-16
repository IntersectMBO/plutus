# deployment-server

The deployment server is used to automatically deploy the playgrounds when a pull request is merged. It listens for the github `pull_request` web hook, if the event has the `merged_at` attribute set then it will `nixops deploy` the `origin/master` branch (or an alternative branch that can be set in the config) from where it is running.

Note that for simplicity it will exclude the `nixops` machine (which is where the deployment server runs) so if you make changes to that machine configuration you will need to deploy manually. One of the issues is that if a change is made to the deployment server service then it will restart _during_ the deployment and end the deployment early.

## Deployment

The deployment server is run on the nixops server however it is only enabled if the `githubWebhookKey` is present in `secrets.json`.

The deployment server relies on a nixops deployment called `playgrounds` existing (this name is configurable). The reason for this is that it's difficult to manage ssh keys for the service however when a deployment is created the keys it is created with are stored in the state. 

What this means is that it's possible to get into a sticky situation if you use an ssh agent to manage multiple identities on your computer. The best thing to do is to check `plutus/deployment/terraform/variables.tf` to see what key `playground_ssh_keys` uses. These keys are the ones that are accepted as a root user for all machines. Then when you login to the nixops machine to create or deploy a deployment you should explicitly select this identity, e.g. `ssh -i ~/.ssh/thisprivatekey -J bastion@thebastion -A root@thenixopsmachine`.

Additionally this means you can rollback the deployment manually etc. Hopefully you called your original deployment `playgrounds` however if you didn't you can just create a new deployment with that name and `nixops delete` the old one with the `--force` flag set.

If you're using the deployment server then whenever you deploy manually you will need to do `nixops modify ./default.nix ./network.nix -d playgrounds` first. Otherwise you will get some sort of confusing error such as
```
[root@nixops:~]# nixops deploy
error: getting status of '/tmp/deployment-6973bf624e21ca85/plutus/deployment/nixops/default.nix': No such file or directory
error: evaluation of the deployment specification failed
```

## Security

As far as I understand, the service needs to be run as root in order to run the deployment so there are limits on how much we can lock down this service. This is because nixops itself requires root access to all the servers although I could be wrong and this might be worth revisiting in the future, especially if we want to use continuous delivery for non-alpha environments.

## Allowing new users to deploy to an existing environment

To complete this you will need the secrets that the environment requires, so make sure you know someone who has these before you carry on. Anyone who can access the root account of the nixops machine can get these from the existing deployments `secrets.json` file. 

Anyone who is able to `terraform apply` to a specific environment can also carry out manual deployments to that environment, debug etc. To do this they will need ssh access to the nixops machine though. Add the person's key to the variable `playground_ssh_keys` in `plutus/deployment/terraform/variables.tf`. Now you will need to `terraform apply`. This will recreate the entire nixops machine so it will probably take a while. Also don't panic if you can't immediately login to the nixops machine after recreating it, in the background a nixos rebuild is happening to add your ssh key and this can take some time, go and have a cup of tea.

Now you need to follow the documentation to [configure the machines](https://github.com/input-output-hk/plutus/tree/master/deployment#configure-the-machines). And that's it, you can test it out by logging on to the nixops server and running `journalctl -fu deploymentServer` then in another terminal running `curl -H "X-Hub-Signature: sha1=thesah1ofthisfile" -H "X-GitHub-Event: pull_request" -H "Content-Type: application/json" -v https://alpha.goguen.monitoring.iohkdev.io/github --data-binary @pr-test.json`

In order to get the `X-Hub-Signature` sha1 you need to run `cat pr-test.json | openssl dgst -sha1 -hex -hmac "thegithubWebhookKey"` which creates a signature of the file with the `githubWebhookKey` from the deployment server.