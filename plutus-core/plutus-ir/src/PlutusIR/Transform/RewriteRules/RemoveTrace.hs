{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

module PlutusIR.Transform.RewriteRules.RemoveTrace
  ( rewriteRuleRemoveTrace
  ) where

import PlutusCore.Default (DefaultFun)
import PlutusCore.Default.Builtins qualified as Builtin
import PlutusIR.Transform.RewriteRules.Common (pattern A, pattern B, pattern I)
import PlutusIR.Transform.RewriteRules.Internal (RewriteRules (..))

{- Note [Impure trace messages]

Removing of traces could change behavior of those programs that use impure trace messages
e.g. `trace (error ()) foo`.

While it is possible to force evaluation of a trace message when removing a trace call
for the sake of a behavior preservation, this has a downside that pure messages remain
in the program and are not elimitated as a "dead" code.

This downside would defeat the purpose of removing traces, so we decided to not force.
-}

rewriteRuleRemoveTrace :: RewriteRules uni DefaultFun
rewriteRuleRemoveTrace = RewriteRules \_varsInfo -> \case
  B Builtin.Trace `I` _argTy `A` _msg `A` arg -> pure arg
  term -> pure term
