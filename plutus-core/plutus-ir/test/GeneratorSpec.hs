-- editorconfig-checker-disable-file
module GeneratorSpec where

import GeneratorSpec.Substitution
import GeneratorSpec.Types

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.QuickCheck

-- | The PIR generators test suite. The argument allows the caller to scale the number of tests.
-- The default for the argument is @1@.
generators :: Int -> TestNested
generators factor = return $ testGroup "generators"
  [ testProperty "prop_genKindCorrect"  $ withMaxSuccess (factor*100000) (prop_genKindCorrect False)
  , testProperty "prop_shrinkTypeSound" $ withMaxSuccess (factor*100000) prop_shrinkTypeSound
  , testProperty "prop_substType"       $ withMaxSuccess (factor*10000) prop_substType
  , testProperty "prop_unify"           $ withMaxSuccess (factor*10000) prop_unify
  ]
