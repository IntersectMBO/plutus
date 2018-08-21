module Language.PlutusCore.PrettyCfg ( PrettyCfg (..)
                                     , Configuration (..)
                                     ) where

import           PlutusPrelude

data Configuration = Configuration { _debug :: Bool, _annotation :: Bool }

class PrettyCfg a where
    prettyCfg :: Configuration -> a -> Doc a
