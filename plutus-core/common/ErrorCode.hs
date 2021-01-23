module ErrorCode
    ( HasErrorCode(..)
    , ErrorCode(..)
    ) where

import           Data.Text.Prettyprint.Doc
import           Numeric.Natural
import           Text.Printf

{- Note [Error Codes of plutus errors]

Our goal is to assign a project-wide unique error number (errorCode) to all errors
that might occur during any phase of compilation --- lifting values, compiling Plutus Tx,
compiling PIR, executing PLC, "off-chain" Plutus code ---, so
as to document and easily identify these errors.

We drew inspiration from `rustc` compiler error-codes:
<https://doc.rust-lang.org/nightly/nightly-rustc/rustc_errors/index.html>

Related work on error hierarchy, error annotations for haskell:
<https://gitlab.haskell.org/ghc/ghc/-/wikis/Errors-as-(structured)-values>
<https://github.com/ghc-proposals/ghc-proposals/pull/307>

An errorcode is a positive number (`Natural`) assigned to every possible data-constructor
that represents an exceptional case. This may include both pure error-values raised
by e.g. `ExceptT` but also "impure" ghc-builtin Control.Exception instances.

For that we created a class `ErrorCode` with one method `errorCode`,
left to be implemented for each error by the Plutus developers.
It is the responsibility of the  Plutus developer to make sure that

1) the assigned errorcode (Natural) is unique among the whole Plutus-project codebase,
2) the `errorCode` method is total
3) no "wrapper-constructors" are tagged. e.g.in:

```data PirError =
    WrapperTC PIR.TCError
    | WrapperParse  PIR.ParseError
    | PirCompile String
```

We do not uniquely tag the wrapper-constructors WrapperTC,WrapperParse,WrapperCompile,
we only tag the "base error constructor" PirCompile:

```
instance HasErrorCode PirError where
   errorCode PirCompile {} = 9997
   errorCode (WrapperTC e) = errorCode e
   errorCode (WrapperParse e) = errorCode e
```

A Plutus sub-project that wants to throw an error, must depend on this package `plutus-core`.
To aid in defining an instance for a brand-new (uncategorized) error or added error-dataconstructors,
the Plutus developer can make use (but not cabal-depend upon) of the
mega-package plutus-errors to "guess-pick" an error-code that is not currently in use
by the whole codebase, by running

```
> cabal run plutus-errors-next
An error code that is not currently used is: 9998
```

After defining/extending this errorcode instance, the Plutus developer must navigate to the megapackage and
confirm these new errorcodes by adding all newly-introduced base-error constructors
to the list of all-project errors `plutus-errors/src/Errors.hs`. The TH code of `plutus-errors`
will make sure there are not duplicates, and running the `cabal haddock plutus-errors`
will build the documentation of all (categorized) errors.

When an error is deprecated (does not trigger anymore) and (some of) its dataconstructors has been removed,
and in case the error is "exposed" to the public, then it is required that its "deprecated" constructors
be "moved" and listed/errorCoded under the umbrella datatype `plutus-errors:Errors.DeprecatedErrors`.
The reason for this is to document/keep track of deprecated errors and not *re*-pick "old" error-codes.

Currently all errors among the project are placed into one big pile of error-codes. We later
might use sub-groups of error-codes with specific ranges, e.g. (PIR : 0000 - 0100, PLC: 0100 - 0200, etc), which then would require
to put into use the "wrapper-constructors" of our error-grouppings.
-}

-- | Assigns an error-code to data-constructors (values) of error types.
-- Note, when implementing this method you're only supposed to look at
-- the outermost constructor (whnf) of the 'a' value to decide for the error-code.
class HasErrorCode a where
    errorCode :: a -> ErrorCode

-- | A wrapper to Natural so as to override the pretty instance of Natural with zero padding
newtype ErrorCode = ErrorCode Natural
    deriving newtype (Eq, Ord, Enum)

instance Pretty ErrorCode where
    pretty (ErrorCode n) = pretty (printf "E%03d" n :: String)
