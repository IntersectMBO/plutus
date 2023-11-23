module PlutusIR.Transform.CaseReduce.Tests where

import Data.Functor.Identity
import PlutusIR.Pass.Test
import PlutusIR.Transform.CaseReduce
import Test.QuickCheck.Property (Property, withMaxSuccess)

prop_caseReduce :: Property
prop_caseReduce = withMaxSuccess 3000 $ testPassProp runIdentity caseReducePass
