#!/usr/bin/env bash

if [[ $# -ne 1 ]]; then
    echo "[deploy.sh] Environment to deploy to has not been specified!"
    echo "[deploy.sh] Exiting."
    exit 1
else
    DEPLOY_ENV="$1"
    echo "[deploy.sh] Deploying to '$DEPLOY_ENV'"
fi

# -----------------------------------------------------------------------------
# sanity checks
# -----------------------------------------------------------------------------

echo "[deploy.sh] Sanity checking env variables"

if [ -n "$PLUTUS_CI_AWS_ACCESS_KEY_ID" ]; then
    echo "[deploy.sh] PLUTUS_CI_AWS_ACCESS_KEY_ID is set"
else
    echo "[deploy.sh] PLUTUS_CI_AWS_ACCESS_KEY_ID is NOT set"
    exit 1
fi

if [ -n "$PLUTUS_CI_AWS_SECRET_ACCESS_KEY" ]; then
    echo "[deploy.sh] PLUTUS_CI_AWS_SECRET_ACCESS_KEY is set"
else
    echo "[deploy.sh] PLUTUS_CI_AWS_SECRET_ACCESS_KEY is NOT set"
    exit 1
fi

if [ -n "$PLUTUS_CI_PRIVATE_SSH" ]; then
    echo "[deploy.sh] PLUTUS_CI_PRIVATE_SSH is set"
else
    echo "[deploy.sh] PLUTUS_CI_PRIVATE_SSH is NOT set"
    exit 1
fi

# -----------------------------------------------------------------------------
# setup
# -----------------------------------------------------------------------------

export AWS_ACCESS_KEY_ID="$PLUTUS_CI_AWS_ACCESS_KEY_ID"
export AWS_SECRET_ACCESS_KEY="$PLUTUS_CI_AWS_SECRET_ACCESS_KEY"

echo "[deploy.sh] Adding ssh key"
eval "$(ssh-agent)"
ssh-add - <<< "${PLUTUS_CI_PRIVATE_SSH}"
ssh-add -l

# -----------------------------------------------------------------------------
# starting deployment
# -----------------------------------------------------------------------------

cd deployment && nix-shell -A "$DEPLOY_ENV" --run "deploy-nix"
