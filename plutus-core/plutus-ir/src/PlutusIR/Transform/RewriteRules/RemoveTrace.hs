{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE PatternSynonyms #-}

module PlutusIR.Transform.RewriteRules.RemoveTrace
  ( rewriteRuleRemoveTrace
  ) where

import PlutusCore.Default (DefaultFun)
import PlutusCore.Default.Builtins qualified as Builtin
import PlutusIR.Transform.RewriteRules.Common (pattern A, pattern B, pattern I)
import PlutusIR.Transform.RewriteRules.Internal (RewriteRules (..))

rewriteRuleRemoveTrace :: RewriteRules uni DefaultFun
rewriteRuleRemoveTrace = RewriteRules \_varsInfo -> \case
  B Builtin.Trace `I` _ty `A` _msg `A` arg -> pure arg
  term -> pure term
