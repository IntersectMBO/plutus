{-# LANGUAGE TemplateHaskell #-}

module UntypedPlutusCore.Simplify.Opts
  ( SimplifyOpts (..)
  , soMaxSimplifierIterations
  , soMaxCseIterations
  , soInlineHints
  , soConservativeOpts
  , soInlineConstants
  , defaultSimplifyOpts
  ) where

import Control.Lens.TH (makeLenses)
import PlutusCore.Annotation (Inline (..), InlineHints (..))

data SimplifyOpts name a = SimplifyOpts
  { _soMaxSimplifierIterations :: Int
  , _soMaxCseIterations        :: Int
  , _soConservativeOpts        :: Bool
  , _soInlineHints             :: InlineHints name a
  , _soInlineConstants         :: Bool
  }
  deriving stock (Show)

$(makeLenses ''SimplifyOpts)

defaultSimplifyOpts :: SimplifyOpts name a
defaultSimplifyOpts =
  SimplifyOpts
    { _soMaxSimplifierIterations = 12
    , _soMaxCseIterations = 4
    , _soConservativeOpts = False
    , _soInlineHints = InlineHints (\_ _ -> MayInline)
    , _soInlineConstants = True
    }
