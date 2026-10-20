{-| Timing of Plinth compilation stages through GHC's own timing infrastructure.

Each stage is wrapped in 'GHC.Utils.Error.withTiming', so it is reported alongside GHC's
own phases under @-ddump-timings@ (or @-v2@) and emits begin/end events to the eventlog. -}
module PlutusTx.Plugin.Timing (timeStage, timingsEnabled) where

import Control.Monad.IO.Class (MonadIO)
import GHC.Driver.Flags (DumpFlag (Opt_D_dump_timings))
import GHC.Utils.Error (withTiming)
import GHC.Utils.Logger (Logger, logHasDumpFlag, logVerbAtLeast)
import GHC.Utils.Outputable (brackets, text, (<+>))

{-| Time an action as the phase @Plinth \<stage\> [\<scope\>]@.

When timings are off this is just the action. When they are on, the result is
evaluated to WHNF and, if forcing is requested, further with the given function
before the clocks stop. -}
timeStage
  :: MonadIO monad
  => Logger
  -> Bool
  -- ^ Whether to force the result with the given function.
  -> String
  -- ^ Module or expression scope.
  -> String
  -- ^ Stage name.
  -> (result -> ())
  -- ^ Forces the result; only called when timings are on and forcing is requested.
  -> monad result
  -- ^ Action to measure.
  -> monad result
timeStage logger forceResults scope stage forceResult =
  withTiming
    logger
    (text "Plinth" <+> text stage <+> brackets (text scope))
    (if forceResults then forceResult else const ())

-- | Whether GHC will report timings: the same condition 'withTiming' checks.
timingsEnabled :: Logger -> Bool
timingsEnabled logger = logVerbAtLeast logger 2 || logHasDumpFlag logger Opt_D_dump_timings
