{-# LANGUAGE TemplateHaskell #-}

module UntypedPlutusCore.Optimize.Opts
  ( OptimizeOpts (..)
  , ooApplyToCase
  , ooMaxSimplifierIterations
  , ooMaxCseIterations
  , ooCseWhichSubterms
  , ooInlineHints
  , ooConservativeOpts
  , ooInlineConstants
  , ooInlineUnconditionalGrowth
  , ooInlineCallsiteGrowth
  , ooPreserveLogging
  , ooCertifiedOptsOnly
  , defaultOptimizeOpts
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

data OptimizeOpts name a = OptimizeOpts
  { _ooMaxSimplifierIterations :: Int
  , _ooMaxCseIterations :: Int
  , _ooCseWhichSubterms :: CseWhichSubterms
  , _ooConservativeOpts :: Bool
  , _ooInlineHints :: InlineHints name a
  , _ooInlineConstants :: Bool
  , _ooInlineUnconditionalGrowth :: AstSize
  , _ooInlineCallsiteGrowth :: AstSize
  , _ooPreserveLogging :: Bool
  , _ooApplyToCase :: Bool
  , _ooCertifiedOptsOnly :: Bool
  }
  deriving stock (Show)

$(makeLenses ''OptimizeOpts)

defaultOptimizeOpts :: OptimizeOpts name a
defaultOptimizeOpts =
  OptimizeOpts
    { _ooMaxSimplifierIterations = 12
    , _ooMaxCseIterations = 4
    , _ooCseWhichSubterms = ExcludeWorkFree
    , _ooConservativeOpts = False
    , _ooInlineHints = def
    , _ooInlineConstants = True
    , _ooInlineUnconditionalGrowth = 1
    , _ooInlineCallsiteGrowth = 5
    , _ooPreserveLogging = True
    , _ooApplyToCase = True
    , _ooCertifiedOptsOnly = False
    }
