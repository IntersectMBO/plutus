module Rational.Laws (lawsTests) where

import Rational.Laws.Additive (additiveLaws)
import Rational.Laws.Construction (constructionLaws)
import Rational.Laws.Eq (eqLaws)
import Rational.Laws.Module (moduleLaws)
import Rational.Laws.Multiplicative (multiplicativeLaws)
import Rational.Laws.Ord (ordLaws)
import Rational.Laws.Other (otherLaws)
import Rational.Laws.Ring (ringLaws)
import Rational.Laws.Serialization (serializationLaws)
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
