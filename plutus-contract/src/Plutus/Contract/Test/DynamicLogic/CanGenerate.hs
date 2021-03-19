module Plutus.Contract.Test.DynamicLogic.CanGenerate (canGenerate) where

import           System.IO.Unsafe
import           Test.QuickCheck

-- canGenerate prob g p
--   returns False if we are sure Prob(g generates x satisfying p) >= prob
--   otherwise True (and we know such an x can be generated)

canGenerate :: Double -> Gen a -> (a -> Bool) -> Bool
canGenerate prob g p = unsafePerformIO $ tryToGenerate 1
  where tryToGenerate luck
          | luck < eps = return False
          | otherwise  = do x <- generate g
                            if p x then return True else
                              tryToGenerate (luck * (1-prob))

        -- Our confidence level is 1-eps
        eps = 1.0e-9
