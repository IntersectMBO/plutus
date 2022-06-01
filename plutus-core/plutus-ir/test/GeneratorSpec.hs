module GeneratorSpec where

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.QuickCheck

import GeneratorSpec.Substitution
import GeneratorSpec.Terms
import GeneratorSpec.Types

generators :: TestNested
generators = return $ testGroup "generators"
  [ testProperty "prop_genKindCorrect"  $ withMaxSuccess 1000 prop_genKindCorrect
  , testProperty "prop_shrinkTypeSound" $ prop_shrinkTypeSound
  , testProperty "prop_genTypeCorrect"  $ withMaxSuccess 1000 prop_genTypeCorrect
  , testProperty "prop_shrinkTermSound" $ withMaxSuccess 20 prop_shrinkTermSound
  , testProperty "prop_substType"       $ withMaxSuccess 10000 prop_substType
  , testProperty "prop_unify"           $ withMaxSuccess 10000 prop_unify
  -- TODO: make this work.
  -- , testProperty "prop_compile" prop_compile
  ]
