-- | This module contains the 'PrettyCfg' typeclass, a more sophisticated
-- typeclass for pretty-printing that allows us to dump debug information only
-- when wanted.
module Language.PlutusCore.PrettyCfg ( PrettyCfg (..)
                                     , Configuration (..)
                                     -- * Helper functions
                                     , prettyCfgString
                                     , prettyCfgText
                                     , debugText
                                     , defaultCfg
                                     , debugCfg
                                     , renderCfg
                                     ) where

import qualified Data.Text                               as T
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.String (renderString)
import           PlutusPrelude

data Configuration = Configuration { _debug :: Bool, _annotation :: Bool }

class PrettyCfg a where
    prettyCfg :: Configuration -> a -> Doc b

instance PrettyCfg a => PrettyCfg [a] where
    prettyCfg cfg = list . fmap (prettyCfg cfg)

renderCfg :: PrettyCfg a => Configuration -> a -> T.Text
renderCfg = render .* prettyCfg

-- | Render a 'Program' as strict 'Text', using 'defaultCfg'
prettyCfgText :: PrettyCfg a => a -> T.Text
prettyCfgText = render . prettyCfg defaultCfg

defaultCfg :: Configuration
defaultCfg = Configuration False False

debugCfg :: Configuration
debugCfg = Configuration True False

debugText :: PrettyCfg a => a -> T.Text
debugText = render . prettyCfg debugCfg

prettyCfgString :: PrettyCfg a => a -> String
prettyCfgString = renderString . layoutPretty defaultLayoutOptions . prettyCfg defaultCfg
