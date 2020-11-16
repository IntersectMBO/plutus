module Main where

import Language.Marlowe.ACTUS.Agda.GenPayoff
import Language.Marlowe.ACTUS.Agda.GenStateTransition
import Agda.Syntax.Concrete.Pretty ()
import Agda.Utils.Pretty
import Text.PrettyPrint

main :: IO () = do
    let style = Style PageMode 1000 1.5
    writeFile "agda/generated/PayOff.agda" $ renderStyle style $ pretty payoff
    writeFile "agda/generated/StateTransition.agda" $ renderStyle style $ pretty stateTransition