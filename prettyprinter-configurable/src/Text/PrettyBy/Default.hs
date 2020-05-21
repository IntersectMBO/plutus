{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeFamilies   #-}

module Text.PrettyBy.Default
    ( layoutDef
    , RenderDef (..)
    , prettyDef
    , prettyDefBy
    , prettyDefM
    ) where

import           Text.PrettyBy
import           Text.PrettyBy.Monad

import qualified Data.Text                               as Strict
import qualified Data.Text.Lazy                          as Lazy
import           Data.Text.Prettyprint.Doc.Render.String (renderString)
import           Data.Text.Prettyprint.Doc.Render.Text   (renderLazy, renderStrict)
import           Text.Pretty

layoutDef :: Doc ann -> SimpleDocStream ann
layoutDef = layoutSmart defaultLayoutOptions

class RenderDef str where
    renderDef :: Doc ann -> str

instance a ~ Char => RenderDef [a] where
    renderDef = renderString . layoutDef

instance RenderDef Strict.Text where
    renderDef = renderStrict . layoutDef

instance RenderDef Lazy.Text where
    renderDef = renderLazy . layoutDef

-- | Pretty-print a value as a string type.
prettyDef :: forall str a. (Pretty a, RenderDef str) => a -> str
prettyDef = renderDef . pretty

-- | Render a value as 'String'.
prettyDefBy :: forall str a config. (PrettyBy config a, RenderDef str) => config -> a -> str
prettyDefBy config = renderDef . prettyBy config

-- | Render a value as 'String'.
prettyDefM
    :: forall str a m env config. (MonadPretty config env m, PrettyBy config a, RenderDef str)
    => a -> m str
prettyDefM = fmap renderDef . prettyM
