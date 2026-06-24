module PlutusIR.Transform.CaseReduce.Tests where

import Data.Functor.Identity
import PlutusIR.Pass.Test
import PlutusIR.Transform.CaseReduce
import Test.Cardano.Base.QuickCheck qualified as BaseQC
import Test.QuickCheck.Property (Property)

prop_caseReduce :: Property
prop_caseReduce = BaseQC.withNumTests numTestsForPassProp $ testPassProp runIdentity caseReducePass
