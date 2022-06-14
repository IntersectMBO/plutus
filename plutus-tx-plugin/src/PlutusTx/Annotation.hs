module PlutusTx.Annotation where

import GHC.Generics
import Prettyprinter

data Ann
    = -- | When calling @PlutusIR.Compiler.Definitions.defineTerm@ to add a new term definition,
      -- if we annotation the var on the LHS of the definition with `AnnInline`, the inliner will
      -- always inline that var.
      --
      -- This is currently used to ensure builtin functions such as @trace@ (when the @remove-trace@
      -- flag is on and @trace@ is rewritten to @const@) are inlined, because the inliner would
      -- otherwise not inline them. To achieve that, we annotate the definition with `AnnInline`
      -- when defining @trace@, i.e., @trace <AnnInline> = \_ a -> a@.
      AnnInline
    | AnnOther
    deriving stock (Eq, Ord, Generic, Show)

instance Pretty Ann where
    pretty = viaShow
