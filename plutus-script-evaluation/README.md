# Plutus Script Evaluation

This package provides tools to gather real-world script events from the Cardano blockchain network (typically 'mainnet'). These events can then be used in tests to validate assumptions about Plutus scripts against their actual behavior on the network.

## Script Dump Job

An executable `dump-script-events` is provided that can be used to dump script events from the Cardano blockchain network. 

The progam will connect to a Cardano node and listen for new blocks. For each block, it will extract all the script events from the transactions in the block and write them to a file.

Script dump job stores "checkpoint" files such that it can resume from the last checkpoint created. This is useful in case the program execution is interrupted and needs to be restarted.

```
Usage: dump-script-events --socket-path SOCKET_PATH --config CONFIG_PATH 
                          (--mainnet | --testnet-magic NATURAL)
                          --blocks-per-file BLOCKS_PER_FILE 
                          [--events-per-file EVENTS_PER_FILE]
                          --dump-dir DUMP_DIR --checkpoint-dir CHECKPOINT_DIR

Available options:
  --socket-path SOCKET_PATH
                           Node socket path
  --config CONFIG_PATH     Node config path
  --mainnet                Use the mainnet magic id.
  --testnet-magic NATURAL  Specify a testnet magic id.
  --blocks-per-file BLOCKS_PER_FILE
                           Write events in this many blocks per file (unless
                           events-per-file is exceeded)
  --events-per-file EVENTS_PER_FILE
                           Write approximately this many events per file (unless
                           blocks-per-file is exceeded)
  --dump-dir DUMP_DIR      Directory to dump the events to
  --checkpoint-dir CHECKPOINT_DIR
                           Directory to store the checkpoint files
  -h,--help                Show this help text
```
