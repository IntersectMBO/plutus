{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeOperators  #-}

-- | Default rendering to string types.

module Text.PrettyBy.Default
    ( layoutDef
    , Render (..)
    , display
    , displayBy
    ) where

import Text.Pretty
import Text.PrettyBy.Internal

import Data.Text qualified as Strict
import Data.Text.Lazy qualified as Lazy
import Prettyprinter.Render.String (renderString)
import Prettyprinter.Render.Text (renderLazy, renderStrict)

-- | A default layout for default rendering.
layoutDef :: Doc ann -> SimpleDocStream ann
layoutDef = layoutSmart defaultLayoutOptions

-- | A class for rendering 'Doc's as string types.
class Render str where
    -- | Render a 'Doc' as a string type.
    render :: Doc ann -> str

instance a ~ Char => Render [a] where
    render = renderString . layoutDef

instance Render Strict.Text where
    render = renderStrict . layoutDef

instance Render Lazy.Text where
    render = renderLazy . layoutDef

-- | Pretty-print and render a value as a string type.
display :: forall str a. (Pretty a, Render str) => a -> str
display = render . pretty

-- | Pretty-print and render a value as a string type in a configurable way.
displayBy :: forall str a config. (PrettyBy config a, Render str) => config -> a -> str
displayBy config = render . prettyBy config
