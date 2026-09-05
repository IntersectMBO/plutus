module Certifier.Common where

import Control.Lens ((&), (.~))
import Control.Monad.Trans.Except
import Data.ByteString qualified as B
import Data.ByteString.Short qualified as SBS
import FFI.OptimizerTrace
import FFI.Untyped (UTerm)
import PlutusBenchmark.Common (getDataDir)
import PlutusCore.Default.Builtins
import PlutusCore.Quote
import PlutusLedgerApi.Common
import System.FilePath
import UntypedPlutusCore as UPLC

-- | Load a UPLC term from a flat-encoded script in the benchmark data directory.
loadTermFrom :: FilePath -> IO (Term Name DefaultUni DefaultFun ())
loadTermFrom name = do
  root <- getDataDir
  prog <-
    UPLC.programMapNames UPLC.fakeNameDeBruijn . uncheckedDeserialiseUPLC . SBS.toShort
      <$> B.readFile (root </> "certifier" </> "data" </> name)
  pure
    . either
      ( \e ->
          error $
            "Certifier.Common.loadTermFrom: program from "
              <> name
              <> " is ill-scoped: "
              <> show e
      )
      id
    . runQuote
    . runExceptT
    $ UPLC.unDeBruijnTerm (UPLC._progTerm prog)

loadFrom :: FilePath -> IO (Trace UTerm)
loadFrom name = do
  term <- loadTermFrom name
  pure . runQuote $ mkFfiOptimizerTrace . snd <$> simplify term

simplify
  :: Term Name DefaultUni DefaultFun ()
  -> Quote
       ( Term Name DefaultUni DefaultFun ()
       , OptimizerTrace Name DefaultUni DefaultFun ()
       )
simplify =
  runOptimizerT
    . termOptimizer
      ( defaultOptimizeOpts
          & ooPreserveLogging .~ False
      )
      DefaultFunSemanticsVariantE

{-| The inline-pass instances recorded in an optimizer trace, in the order the
inliner ran on them. An instance is a triple of the term the inliner was given,
the certifier annotations ("hints") it emitted, and the term it produced.

Shared by the measurement tools so that they agree on what an inline instance
is. Under 'simplify' each script yields one instance per simplifier run. -}
inlineInstances
  :: OptimizerTrace Name DefaultUni DefaultFun ()
  -> [Optimization Name DefaultUni DefaultFun ()]
inlineInstances tr =
  -- `optimizerTrace` is in reverse order: the first item is the last pass run.
  reverse [o | o@(Optimization _ InlineStage _ _) <- optimizerTrace tr]

testScripts :: [FilePath]
testScripts =
  [ "n-queens.uplc"
  , "coop.uplc"
  , "linear-vesting.uplc"
  , "cardano-loans.uplc"
  , "marlowe-semantics.uplc"
  , "marlowe-semantics-data.uplc"
  , "marlowe-rolepayout.uplc"
  , "marlowe-rolepayout-data.uplc"
  , "guardrail-sorted.uplc"
  , "guardrail-unsorted.uplc"
  , "guardrail-sorted-data.uplc"
  , "guardrail-unsorted-data.uplc"
  ]
