-- | This module contains the 'PrettyCfg' typeclass, a more sophisticated
-- typeclass for pretty-printing that allows us to dump debug information only
-- when wanted.
module Language.PlutusCore.PrettyCfg ( PrettyCfg (..)
                                     , Configuration (..)
                                     -- * Helper functions
                                     , prettyText
                                     , prettyCfgString
                                     , debugText
                                     , defaultCfg
                                     , debugCfg
                                     ) where

import qualified Data.Text                               as T
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.String (renderString)
import           PlutusPrelude

data Configuration = Configuration { _debug :: Bool, _annotation :: Bool }

class PrettyCfg a where
    prettyCfg :: Configuration -> a -> Doc b

-- | Render a 'Program' as strict 'Text'.
prettyText :: PrettyCfg a => a -> T.Text
prettyText = render . prettyCfg defaultCfg

defaultCfg :: Configuration
defaultCfg = Configuration False False

debugCfg :: Configuration
debugCfg = Configuration True False

debugText :: PrettyCfg a => a -> T.Text
debugText = render . prettyCfg debugCfg

prettyCfgString :: PrettyCfg a => a -> String
prettyCfgString = renderString . layoutPretty defaultLayoutOptions . prettyCfg defaultCfg
