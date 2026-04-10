{-# LANGUAGE TemplateHaskell #-}

module UntypedPlutusCore.Simplify.Opts
  ( SimplifyOpts (..)
  , soApplyToCase
  , soMaxSimplifierIterations
  , soMaxCseIterations
  , soCseWhichSubterms
  , soInlineHints
  , soConservativeOpts
  , soInlineConstants
  , soInlineCallsiteGrowth
  , soPreserveLogging
  , soOptBias
  , defaultSimplifyOpts
  , OptBias
  , unOptBias
  , optBias
  ) where

import Control.Lens.TH (makeLenses)
import Data.Default.Class

import PlutusCore.Annotation (InlineHints (..))
import PlutusCore.AstSize
import UntypedPlutusCore.Transform.Cse (CseWhichSubterms (..))

newtype OptBias = OptBias {unOptBias :: Int}
  deriving newtype (Show, Eq, Ord, Num)

optBias :: Int -> OptBias
optBias = OptBias . max 0 . min 4

data SimplifyOpts name a = SimplifyOpts
  { _soMaxSimplifierIterations :: Int
  , _soMaxCseIterations :: Int
  , _soCseWhichSubterms :: CseWhichSubterms
  , _soConservativeOpts :: Bool
  , _soInlineHints :: InlineHints name a
  , _soInlineConstants :: Bool
  , _soInlineCallsiteGrowth :: AstSize
  , _soPreserveLogging :: Bool
  , _soApplyToCase :: Bool
  , _soOptBias :: OptBias
  }
  deriving stock (Show)

$(makeLenses ''SimplifyOpts)

defaultSimplifyOpts :: SimplifyOpts name a
defaultSimplifyOpts =
  SimplifyOpts
    { _soMaxSimplifierIterations = 12
    , _soMaxCseIterations = 4
    , _soCseWhichSubterms = ExcludeWorkFree
    , _soConservativeOpts = False
    , _soInlineHints = def
    , _soInlineConstants = True
    , _soInlineCallsiteGrowth = 5
    , _soPreserveLogging = True
    , _soApplyToCase = True
    , _soOptBias = optBias 2
    }
