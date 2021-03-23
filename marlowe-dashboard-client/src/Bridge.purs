module Bridge
  ( slotToMarlowe
  ) where

import Marlowe.Semantics (Slot(..)) as Marlowe
import Plutus.V1.Ledger.Slot (Slot(..)) as Plutus

slotToMarlowe :: Plutus.Slot -> Marlowe.Slot
slotToMarlowe slot@(Plutus.Slot { getSlot }) = Marlowe.Slot getSlot
