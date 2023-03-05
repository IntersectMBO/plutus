module PlutusCore.BLS12_381.Pairing
    (
     pairing
    ) where

import PlutusCore.BLS12_381.G1 qualified as G1
import PlutusCore.BLS12_381.G2 qualified as G2
import PlutusCore.BLS12_381.GT qualified as GT

-- Partial pairing Miller loop
pairing
    :: G1.Element
    -> G2.Element
    -> GT.Element
pairing = undefined
