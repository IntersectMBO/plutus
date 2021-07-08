# Plutus chain index

The chain index is a program that follows the cardano blockchain and stores information from the chain in a database.
The information that is stored is useful for Plutus smart contracts: Various hash values and transaction information.

The chain index is intended to be used primarily by the PAB, but its HTTP interface can be accessed by other applications also.

## Design goals

- Minimise RAM usage
  - Keep most data on disk and store only the tx out references in RAM
- Allow for time and space efficient query answering
  - Most queries are single lookups in a key-value store
  - The maximum size of responses to chain index queries is fixed and independent of the UTXO set
- Allow for for fast updating of the utxo set
  - Rollbacks can be processed in log time (relative to the chain constant `k`)
  - Deletion of old data from disk storage can be performed out-of-band (garbage collection style)
- Allow for fast initial indexing
  - Chunks of transactions can be processed in parallel while the chain index is catching up
- Limit disk usage
  - Disk storage required is proportional to UTXO set, *not* to the length of the chain

