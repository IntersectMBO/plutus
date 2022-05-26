module PlutusTx.Annotation where

import GHC.Generics
import Prettyprinter

data Ann
    = -- | When a term `t` has this annotation, the inliner will inline bindings `var = t`.
      -- This is currently used to make sure builtin functions `trace` (when `remove-trace`
      -- is specified) and `error` are inlined.
      AnnInline
    | AnnOther
    deriving stock (Eq, Ord, Generic, Show)

instance Pretty Ann where
    pretty = viaShow
