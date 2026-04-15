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
  , soSafeOpts
  , defaultSimplifyOpts
  , CseWhichSubterms (..)
  ) where

import Control.Lens.TH (makeLenses)
import Data.Default.Class

import PlutusCore.Annotation (InlineHints (..))
import PlutusCore.AstSize
import PlutusCore.Pretty
import Prettyprinter (viaShow)

-- | Which subterms should be considered as candidates for CSE?
data CseWhichSubterms = AllSubterms | ExcludeWorkFree
  deriving stock (Show, Read)

instance Pretty CseWhichSubterms where
  pretty = viaShow

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
  , _soSafeOpts :: Bool
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
    , _soSafeOpts = False
    }
