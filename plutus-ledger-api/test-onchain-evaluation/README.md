# Plutus On-Chain Script Evaluation Tests

This test suite evaluates Plutus scripts that ran on the Cardano mainnet.
It verifies the preservation of behavior: existing scripts that succeeded (resp. failed) on-chain on a given input should always continue to succeed (resp. fail) when evaluated on plutus master given the same input.

The test suite currently runs nightly.

## Generating Script Dumps

The executable for generating script dumps is in the [plutus-apps](https://github.com/input-output-hk/plutus-apps) repo, since it depends on the node API.
It is currently in the "plutus-script-dump" branch and will eventually be merged into the main branch.

To run it, check out the "plutus-script-dump" branch, and run the following in the nix shell of plutus-apps:

```
AWS_ACCESS_KEY_ID=<replace_with_aws_key_id> \
AWS_SECRET_ACCESS_KEY=<replace_with_aws_secret_access_key> \
AWS_DEFAULT_REGION=us-east-1 \
AWS_ENDPOINT_URL=https://s3.devx.iog.io \
S3_DUMP_DIR=s3://plutus/mainnet-script-dump/ \
cabal run plutus-script-evaluation-test:dump-script-events -- \
--socket-path $HOME/mainnet/db/node.socket \
--config $HOME/mainnet/mainnet-config.json \
--mainnet \
--blocks-per-file 50000 \
--events-per-file 50000 \
--dir $HOME/cardano-dump
```

Adjust the `socket-path`, `config` and `dir` arguments as appropriate.
The `dir` argument is the local working directory, which will contain the checkpoint files and the dump files.

With the above arguments, it creates one checkpoint file and one dump file per 50000 blocks or 50000 script evaluation events, whichever comes sooner.
When the executable starts, if there are checkpoint files in the working directory, it will resume from the latest checkpoint file.
It keeps the latest 3 checkpoint files and deletes the older ones, since checkpoint files are large.
Upon creating a dump file, it uploads the dump file to `S3_DUMP_DIR` before deleting the local copy.

To ensure that no script evaluation event is lost, it creates and uploads the dump file before writing the checkpoint file.
This means if the job is killed after uploading a dump file but before writing the checkpoint file, it may lead to duplicate events being uploaded.
However, this will only happen if the job is re-started with a different `blocks-per-file` or `events-per-file`.
If both arguments are the same, it will generate the same dump file again, and uploading it will overwrite the previously uploaded one.
This also means that as long as `blocks-per-file` and `events-per-file` remain the same, it is safe to re-run the job from an older checkpoint or the beginning, without producing duplicate dumps on S3.

## Running the Tests

To run the tests, first download the dump files from S3 to a local directory:

```
AWS_ACCESS_KEY_ID=<replace_with_aws_key_id> \
AWS_SECRET_ACCESS_KEY=<replace_with_aws_secret_access_key> \
AWS_DEFAULT_REGION=us-east-1 \
aws --endpoint-url https://s3.devx.iog.io \
s3 sync s3://plutus/mainnet-script-dump/ $HOME/mainnet-script-dump-downloaded
```

Then unzip all `.bz2` files, and run the following in the nix shell of plutus:

```
EVENT_DUMP_DIR=$HOME/mainnet-script-dump-downloaded cabal run plutus-ledger-api:evaluation-test -- --num-threads=1
```

Adjust `EVENT_DUMP_DIR` as appropriate.

The purpose of `--num-threads=1` is to run the tests on one dump file at a time.
Currently, incremental deserialization is not implemented, and each dump file has to be entirely loaded in memory, and this ensures we don't consume too much memory by loading multiple dump files simultaneously.
