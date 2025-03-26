{-# LANGUAGE TemplateHaskell #-}

module UntypedPlutusCore.Simplify.Opts
  ( SimplifyOpts (..)
  , soMaxSimplifierIterations
  , soMaxCseIterations
  , soInlineHints
  , soConservativeOpts
  , soInlineConstants
  , soInlineThreshold
  , defaultSimplifyOpts
  ) where

import Control.Lens.TH (makeLenses)
import Data.Default.Class
import PlutusCore.Annotation (InlineHints (..))

data SimplifyOpts name a = SimplifyOpts
  { _soMaxSimplifierIterations :: Int
  , _soMaxCseIterations        :: Int
  , _soConservativeOpts        :: Bool
  , _soInlineHints             :: InlineHints name a
  , _soInlineConstants         :: Bool
  , _soInlineThreshold         :: Int
  }
  deriving stock (Show)

$(makeLenses ''SimplifyOpts)

defaultSimplifyOpts :: SimplifyOpts name a
defaultSimplifyOpts =
  SimplifyOpts
    { _soMaxSimplifierIterations = 12
    , _soMaxCseIterations = 4
    , _soConservativeOpts = False
    , _soInlineHints = def
    , _soInlineConstants = True
    , _soInlineThreshold = 12
    }
