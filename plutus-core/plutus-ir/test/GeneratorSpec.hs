-- editorconfig-checker-disable-file
module GeneratorSpec where

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.QuickCheck

import GeneratorSpec.Substitution
import GeneratorSpec.Types

generators :: Int -> TestNested
generators factor = return $ testGroup "generators"
  [ testProperty "prop_genKindCorrect"  $ withMaxSuccess (factor*100000) (prop_genKindCorrect False)
  , testProperty "prop_shrinkTypeSound" $ withMaxSuccess (factor*100000) prop_shrinkTypeSound
  , testProperty "prop_substType"       $ withMaxSuccess (factor*10000) prop_substType
  , testProperty "prop_unify"           $ withMaxSuccess (factor*10000) prop_unify
  ]
