This directory contains CBOR-encoded Plutus Core scripts involved
in validation in the `plutus-use-cases` tests.  The validators,
datum scripts, redeemers and contexts have all been extracted into
separate files.  In the tests, some of the scripts appear in
mulitple validations and some validations occur multiple times
Only a single copy of each script has been kept: each subdirectory has
a README file explaining which scripts are involved in each validation.