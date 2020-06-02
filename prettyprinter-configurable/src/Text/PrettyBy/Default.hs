{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeFamilies   #-}

module Text.PrettyBy.Default
    ( layoutDef
    , Render (..)
    , display
    , displayBy
    ) where

import           Text.Pretty
import           Text.PrettyBy.Internal

import qualified Data.Text                               as Strict
import qualified Data.Text.Lazy                          as Lazy
import           Data.Text.Prettyprint.Doc.Render.String (renderString)
import           Data.Text.Prettyprint.Doc.Render.Text   (renderLazy, renderStrict)

layoutDef :: Doc ann -> SimpleDocStream ann
layoutDef = layoutSmart defaultLayoutOptions

class Render str where
    render :: Doc ann -> str

instance a ~ Char => Render [a] where
    render = renderString . layoutDef

instance Render Strict.Text where
    render = renderStrict . layoutDef

instance Render Lazy.Text where
    render = renderLazy . layoutDef

-- | Pretty-print a value as a string type.
display :: forall str a. (Pretty a, Render str) => a -> str
display = render . pretty

-- | Render a value as 'String'.
displayBy :: forall str a config. (PrettyBy config a, Render str) => config -> a -> str
displayBy config = render . prettyBy config
