module Main where

import Language.Marlowe.ACTUS.Agda.GenPayoff
import Language.Marlowe.ACTUS.Agda.GenStateTransition
import Agda.Syntax.Concrete.Pretty ()
import Agda.Utils.Pretty

main :: IO () = do
    writeFile "agda/generated/PayOff.agda" $ show $ pretty payoff
    writeFile "agda/generated/StateTransition.agda" $ show $ pretty stateTransition