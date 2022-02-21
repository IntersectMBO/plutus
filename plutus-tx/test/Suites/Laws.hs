module Suites.Laws (lawsTests) where

import Suites.Laws.Additive (additiveLaws)
import Suites.Laws.Construction (constructionLaws)
import Suites.Laws.Eq (eqLaws)
import Suites.Laws.Module (moduleLaws)
import Suites.Laws.Multiplicative (multiplicativeLaws)
import Suites.Laws.Ord (ordLaws)
import Suites.Laws.Other (otherLaws)
import Suites.Laws.Ring (ringLaws)
import Suites.Laws.Serialization (serializationLaws)
import Test.Tasty (TestTree, testGroup)

lawsTests :: TestTree
lawsTests = testGroup "Rational laws" [
  testGroup "Eq" eqLaws,
  testGroup "Ord" ordLaws,
  testGroup "AdditiveGroup" additiveLaws,
  testGroup "MultiplicativeMonoid" multiplicativeLaws,
  testGroup "Ring" ringLaws,
  testGroup "Module" moduleLaws,
  testGroup "Serialization" serializationLaws,
  testGroup "Construction" constructionLaws,
  testGroup "Other" otherLaws
  ]
