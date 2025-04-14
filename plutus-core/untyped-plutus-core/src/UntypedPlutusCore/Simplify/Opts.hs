{-# LANGUAGE TemplateHaskell #-}

module UntypedPlutusCore.Simplify.Opts
  ( SimplifyOpts (..)
  , soMaxSimplifierIterations
  , soMaxCseIterations
  , soInlineHints
  , soConservativeOpts
  , soInlineConstants
  , soInlineCallsiteGrowth
  , defaultSimplifyOpts
  ) where

import Control.Lens.TH (makeLenses)
import Data.Default.Class

import PlutusCore.Annotation (InlineHints (..))
import PlutusCore.Size

data SimplifyOpts name a = SimplifyOpts
  { _soMaxSimplifierIterations :: Int
  , _soMaxCseIterations        :: Int
  , _soConservativeOpts        :: Bool
  , _soInlineHints             :: InlineHints name a
  , _soInlineConstants         :: Bool
  , _soInlineCallsiteGrowth    :: Size
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
    , _soInlineCallsiteGrowth = 5
    }
