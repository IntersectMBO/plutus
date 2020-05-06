module Debug.Trace.Extra where

import Prelude
import Debug.Trace (class DebugWarning)

-- | Similar to Debug.Trace.trace but also reports the time taken to evaluate the thunk
foreign import traceTime :: forall a b. DebugWarning => a -> (Unit -> b) -> b
