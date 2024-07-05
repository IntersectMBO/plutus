# Plutus Script Dump Job

To run the job, checkout branch `zliu41/dump-1.35.4` in plutus-apps, and run the following in `nix develop`:

```
AWS_ACCESS_KEY_ID=<...> \
  AWS_SECRET_ACCESS_KEY=<...> \
  AWS_DEFAULT_REGION=us-east-1 \
  AWS_ENDPOINT_URL=https://s3.devx.iog.io \
  NODE_DIR=$HOME/mainnet \
  DUMP_DIR=$HOME/mainnet-script-dump \
  S3_DUMP_DIR=s3://plutus/mainnet-script-dump-1-35-4/ \
  CHECKPOINT_DIR=$HOME/mainnet-script-dump-checkpoint \
  S3_CHECKPOINT_DIR=s3://plutus/mainnet-script-dump-1-35-4-checkpoint/ \
  ./scripts/create-dump.sh
```

Fill in the AWS keys, and change the directories as appropriate.

This will run a local mainnet node, dump Plutus scripts into `S3_DUMP_DIR`, and put checkpoint files in `S3_CHECKPOINT_DIR`.

Upon start, it syncs the checkpoint files from S3 and restarts from the latest checkpoint file.
Only the latest two checkpoint files are kept due to their large sizes.
We keep two checkpoint files rather than one in case the latest one is corrupt (e.g., the job is killed while the file is being uploaded), or the latest one is invalid due to a rollback.
