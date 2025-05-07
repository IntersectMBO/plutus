{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes       #-}

module PlutusTx.Test.Util.Compiled (
  Program,
  Term,
  toAnonDeBruijnTerm,
  toAnonDeBruijnProg,
  toNamedDeBruijnTerm,
  compiledCodeToTerm,
  cekResultMatchesHaskellValue,
)
where

import Prelude

import PlutusCore qualified as PLC
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as PLC
import PlutusTx qualified as Tx
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek as Cek

type Term = UPLC.Term PLC.NamedDeBruijn DefaultUni DefaultFun ()
type Program = UPLC.Program PLC.NamedDeBruijn DefaultUni DefaultFun ()

{-| Given a DeBruijn-named term, give every variable the name "v".  If we later
   call unDeBruijn, that will rename the variables to things like "v123", where
   123 is the relevant de Bruijn index.
-}
toNamedDeBruijnTerm
  :: UPLC.Term UPLC.DeBruijn DefaultUni DefaultFun ()
  -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
toNamedDeBruijnTerm = UPLC.termMapNames UPLC.fakeNameDeBruijn

-- | Remove the textual names from a NamedDeBruijn term
toAnonDeBruijnTerm :: Term -> UPLC.Term UPLC.DeBruijn DefaultUni DefaultFun ()
toAnonDeBruijnTerm = UPLC.termMapNames UPLC.unNameDeBruijn

toAnonDeBruijnProg
  :: UPLC.Program UPLC.NamedDeBruijn DefaultUni DefaultFun ()
  -> UPLC.Program UPLC.DeBruijn DefaultUni DefaultFun ()
toAnonDeBruijnProg (UPLC.Program () ver body) =
  UPLC.Program () ver $ toAnonDeBruijnTerm body

{-| Just extract the body of a program wrapped in a 'CompiledCodeIn'.
We use this a lot.
-}
compiledCodeToTerm :: Tx.CompiledCodeIn DefaultUni DefaultFun a -> Term
compiledCodeToTerm code = let UPLC.Program _ _ body = Tx.getPlcNoAnn code in body

{-| Evaluate a PLC term and check that the result matches a given Haskell value
   (perhaps obtained by running the Haskell code that the term was compiled
   from).  We evaluate the lifted Haskell value as well, because lifting may
   produce reducible terms. The function is polymorphic in the comparison
   operator so that we can use it with both HUnit Assertions and QuickCheck
   Properties.
-}
cekResultMatchesHaskellValue
  :: (Tx.Lift DefaultUni hask)
  => Term
  -> (forall r. (Eq r, Show r) => r -> r -> k)
  -> hask
  -> k
cekResultMatchesHaskellValue actual matches expected =
  matches
    (unsafeRunTermCek actual)
    (unsafeRunTermCek (compiledCodeToTerm (Tx.liftCodeDef expected)))
 where
  unsafeRunTermCek :: Term -> EvaluationResult Term
  unsafeRunTermCek =
    unsafeSplitStructuralOperational
      . (\(res, _, _) -> res)
      . runCekDeBruijn
        PLC.defaultCekParametersForTesting
        Cek.restrictingEnormous
        Cek.noEmitter
