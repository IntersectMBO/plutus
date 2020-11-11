module Main where

import Language.Marlowe.ACTUS.Agda.GenPayoff
import Agda.Syntax.Concrete.Pretty ()
import Agda.Utils.Pretty

main :: IO () = do
    writeFile "agda/generated/PayOff.agda" $ show $ pretty payoff