{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}
module PlutusTx.Utils where

-- We do not use qualified import because the whole module contains off-chain code
import PlutusTx.Builtins.Internal qualified as BI
import Prelude as Haskell

mustBeReplaced :: String -> a
mustBeReplaced placeholder =
  error $
    "The " <> show placeholder <> " placeholder must have been replaced by the \
      \core-to-plc plugin during compilation."

-- | Delay evalaution of the expression inside the 'Delay' constructor.
newtype Delay a = Delay (forall b. a)

-- | Force the evaluation of the expression delayed by the 'Delay'.
force :: Delay a -> a
force (Delay a) = a @BI.BuiltinUnit
