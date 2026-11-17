{-| Umbrella re-export of the UAL modules.

'PlutusTx.Ual.TH' is deliberately not re-exported: importing it forces
@TemplateHaskell@ on the importer, and only modules that actually carry
annotations need it. -}
module PlutusTx.Ual (module X) where

import PlutusTx.Ual.Error as X
import PlutusTx.Ual.Parser as X
import PlutusTx.Ual.Resolve as X
import PlutusTx.Ual.Syntax as X
