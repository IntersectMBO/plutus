# plutus-errors: Documentaion of all Plutus-related errors

The `ErrorCode` typeclass under `plutus-core/common/ErrorCode.hs`
assigns a positive number (`Natural`) to every error thrown by Plutus code.
This package provides:

1. A Haddock catalogue of all errors (in-use or obsolete) and their codes `src/Errors/Docs.hs`.
2. A check for duplicates among error codes (implicitly achieved by haddock).
3. An executable `plutus-errors-next` to be used by Plutus developers to fetch a currently-unused error code (number).
4. An executable `plutus-errors-bootstrap` to initialize the codebase with automatically-generated `ErrorCode` instances.

Currently all errors among the project are placed into one big pile of error-codes. We will later
use sub-groups of error-codes with specific ranges, e.g. (PIR : 0000 - 0100, PLC: 0100 - 0200, etc), which then would require
to put into use the "wrapper-constructors" of our error-grouppings.

Run `cabal haddock` to generate the error catalogue.

## Adding a brand-new error

After defining a brand-new Plutus-error and its `ErrorCode` instance, the developer must navigate to `src/Errors.hs` and
update the list of all errors, so as the Haddock documentation can know about it and pick it up.

## Removing an error (making it obsolete)

When an error was exposed to the public but it has
become now obsolete (will never fire anymore) by removing (some of) its dataconstructors,
then the developer should place move these obsolete data-constructors and their respective errorcodes to `src/Errors.hs`
