# Vesting interface example

Build `docusaurus-examples:exe:example-ual-blueprint`, then run
`example-ual-blueprint environment.json`. The producer emits the proposed
compiled-interface blueprint, assurance-v2 and one context per property.
Its Data parameter precedes the V3 context argument; execution settings are
separate from the blueprint.

The checked-in environment is explicitly illustrative, so these snapshots carry
no verification evidence and are not executable as published. Capture an actual
environment with the required CardanoLedgerApi V3 model imports before checking.
The guessing-game example demonstrates a completed fresh verification run.
The broader vesting properties remain a separate verification workload; their
presence in a generated assurance document does not establish them.
