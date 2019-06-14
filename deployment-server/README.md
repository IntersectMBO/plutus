# deployment-server

The deployment server listens for the github `pull_request` web hook, if the event has the `merged_at` attribute set then it will `nixops deploy` the `origin/master` branch from where it is running.

Note that for simplicity it will exclude the `nixops` machine so if you make changes to that machine configuration you will need to deploy manually. One of the issues is that if a change is made to the deployment server service then it will restart _during_ the deployment and end the deployment early.

## Deployment

The deployment server is run on the nixops server however it is only enabled if the `githubWebhookKey` is present in `secrets.json`.

The deployment server relies on a nixops deployment called `playgrounds` existing. The reason for this is that it's difficult to manage ssh keys for the service however when a deployment is created the keys it is created with are stored in the state. Additionally this means you can rollback the deployment manually etc. Hopefully you called your original deployment `playgrounds` however if you didn't you can just create a new deployment with that name and delete the old one with the `--force` flag set.

If you're using the deployment server then whenever you deploy manually you will need to do `nixops modify ./default.nix ./network.nix -d playgrounds` first.

## Security

As far as I understand, the service needs to be run as root in order to run the deployment so there are limits on how much we can lock down this service.