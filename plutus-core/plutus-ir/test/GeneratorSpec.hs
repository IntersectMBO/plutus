-- editorconfig-checker-disable-file
module GeneratorSpec where

import GeneratorSpec.Substitution
import GeneratorSpec.Terms
import GeneratorSpec.Types

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.QuickCheck

-- | The PIR generators test suite. The argument allows the caller to scale the number of tests.
-- The default for the argument is @1@.
generators :: Int -> TestNested
generators factor = return $ testGroup "generators"
  [ testProperty "prop_genKindCorrect" $
      withMaxSuccess (factor*100000) (prop_genKindCorrect False)
  , testProperty "prop_shrinkTypeSound" $
      withMaxSuccess (factor*100000) prop_shrinkTypeSound

  , testProperty "prop_substType" $
      withMaxSuccess (factor*10000) prop_substType
  , testProperty "prop_unify" $
      withMaxSuccess (factor*10000) prop_unify

  , testProperty "prop_genTypeCorrect"  $
      withMaxSuccess (factor*10000) (prop_genTypeCorrect False)
  , testProperty "prop_genWellTypedFullyApplied" $
      withMaxSuccess (factor*1000) prop_genWellTypedFullyApplied
  , testProperty "prop_findInstantiation" $
      withMaxSuccess (factor*10000) prop_findInstantiation
  , testProperty "prop_inhabited" $
      withMaxSuccess (factor*1000) prop_inhabited
  , testProperty "prop_stats_numShrink" $
      withMaxSuccess (factor*10) prop_stats_numShrink
  , testProperty "prop_inhabited" $
      withMaxSuccess (factor*20) prop_noTermShrinkLoops
  , testProperty "prop_shrinkTermSound" $
      withMaxSuccess (factor*20) prop_shrinkTermSound
  ]
