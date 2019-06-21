import qualified Language.PlutusTx as PlutusTx
import Language.PlutusTx (makeLift)
import qualified Language.PlutusTx.Prelude as P
import Ledger
import Ledger.Validation
import qualified Ledger.Value as Value
import Ledger.Value (Value)
import Playground.Contract
import Wallet

import qualified Data.ByteString.Lazy.Char8 as C

data Escrow = Escrow
    { validity :: SlotRange
    , party1 :: (PubKey, Value)
    , party2 :: (PubKey, Value)
    }

makeLift ''Escrow

createDeed :: MonadWallet m => (PubKey, Value) -> (PubKey, Value) -> m DataScript
createDeed party1 party2 = do
    let validity = defaultSlotRange
        escrow = Escrow {..}
    pure $ DataScriptgtpure ()

hold :: MonadWallet m => Value -> m ()
hold value = _

deedValidator :: ValidatorScript
deedValidator = ValidatorScript ($$(Ledger.compileScript [||
  \dataScript validatorScript value ->
    ($$(P.error) ($$(P.traceH) "TODO" ()))
  ||]))

$(mkFunctions ['createDeed, 'hold])
