{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Assertions shared by normal integer properties and conformance generators.
module Evaluation.Builtins.Integer.Conformance
  ( Check (..)
  , GenerateCases
  , generatePropertyFiles
  ) where

import Evaluation.Builtins.Common

import Evaluation.Builtins.Conformance
  ( OutputFormat
  , PropertyId
  , TermCase (..)
  , generateTermFiles
  )

import Test.QuickCheck
  ( Arbitrary (arbitrary)
  , Gen
  , Testable (property)
  , infiniteListOf
  , (.&&.)
  , (==>)
  )
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (QCGen)

{-| Describe a check without performing it. Normal tests interpret it as an
assertion; generation extracts its terms without evaluating the assertion. -}
data Check
  = CheckEq PlcTerm PlcTerm
  | CheckTrue PlcTerm
  | CheckOk PlcTerm
  | CheckFails PlcTerm
  | CheckBoth Check Check
  | CheckImplies Bool Check

instance Testable Check where
  property (CheckEq t1 t2) = evalOkEq t1 t2
  property (CheckTrue t) = evalOkTrue t
  property (CheckOk t) = ok t
  property (CheckFails t) = fails t
  property (CheckBoth a b) = a .&&. b
  property (CheckImplies condition check) = condition ==> check

-- | Sample the inputs of a property without invoking QuickCheck's test runner.
class GenerateCases prop where
  caseGenerator :: prop -> Gen Check

instance GenerateCases Check where
  caseGenerator = pure

instance GenerateCases prop => GenerateCases (Gen prop) where
  caseGenerator gen = gen >>= caseGenerator

instance (Arbitrary a, GenerateCases prop) => GenerateCases (a -> prop) where
  caseGenerator f = arbitrary >>= caseGenerator . f

-- Preconditions still select suitable inputs, but none of the assertions run.
-- Keep this lazy so reaching the case limit need not inspect later checks.
caseTerms :: Check -> [TermCase]
caseTerms (CheckEq t1 t2) = [EqualTerms t1 t2]
caseTerms (CheckTrue t) = [SingleTerm t]
caseTerms (CheckOk t) = [SingleTerm t]
caseTerms (CheckFails t) = [SingleTerm t]
caseTerms (CheckBoth a b) = caseTerms a <> caseTerms b
caseTerms (CheckImplies condition check) = if condition then caseTerms check else []

{-| Export exactly the requested number of cases without running the
property assertions. Terms are sampled lazily using QuickCheck's generators;
sampling stops as soon as the quota is reached. Equality cases emit both terms
with a shared number and -A/-B suffixes. Each exported term is evaluated
once to obtain its expected result and budget. Files from a previous run with
the same names are overwritten; other files are left untouched.

Numbers are padded to five digits. The caller supplies the property identifier,
which carries both the suite segments and the property's own name. Output is placed in:
<property-id-path>/<property-id-name>-<n>[-A|-B]/<property-id-name>-<n>[-A|-B]
with .uplc and/or .flat inputs, matching .expected files, and .budget.expected. -}
generatePropertyFiles
  :: GenerateCases prop
  => OutputFormat
  -> FilePath
  -> Int
  -> QCGen
  -> PropertyId
  -> prop
  -> IO ()
generatePropertyFiles format outputDir numFiles seed propertyId prop =
  generateTermFiles format outputDir numFiles propertyId terms
  where
    -- Match the size used by QuickCheck's 'generate', with an explicit seed.
    cases = unGen (infiniteListOf (caseGenerator prop)) seed 30
    terms = concatMap caseTerms cases
