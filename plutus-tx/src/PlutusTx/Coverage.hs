{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module PlutusTx.Coverage ( CoverageAnnotation(..)
                         , CoverageIndex(..)
                         , coverageAnnotations
                         , addLocationToCoverageIndex
                         , addBoolCaseToCoverageIndex
                         ) where

import           Control.Lens
import qualified FastString           as GHC
import qualified GhcPlugins           as GHC

import           Codec.Serialise

import           PlutusCore.Flat

import           Data.Map             (Map)
import qualified Data.Map             as Map
import           Data.Set             (Set)
import qualified Data.Set             as Set
import           Data.String
import           Text.Read

import           Control.Monad.Writer

import           Prettyprinter

import           Prelude

import           Flat

{- Note [Coverage annotations]
   During compilation we can insert coverage annotations in `trace` calls in
   the PIR code that are tracked in the relevant downstream code by looking at
   the logs. For example, the `LocationCoverage` option piggy-backs on the GHC
   source location annotations (in the form of `Tick`s) and insert `CoverageAnnLocation`
   annotations in the PIR that match the source location in the `Tick`.
-}

{- Note [Adding more coverage annotations]
   To add more coverage annotations we need to:
   1. Add a constructor to `CoverageType`
   2. Add option parsing to the function `parsePluginArgs`
   3. Add a coverage annotation to `CoverageAnn`
   4. Make any necessary modifications to `CoverageIndex`
   5. Add code to the compiler (e.g. in `compileExpr`) to insert
      the `CoverageAnn` and meta-data in the index
-}

-- | A source location for coverage
data CovLoc = CovLoc { _covLocFile      :: String
                     , _covLocStartLine :: Int
                     , _covLocEndLine   :: Int
                     , _covLocStartCol  :: Int
                     , _covLocEndCol    :: Int }
  deriving (Ord, Eq, Show, Read, Generic, Serialise)
  deriving Flat via (AsSerialize CovLoc)

makeLenses ''CovLoc

instance Pretty CovLoc where
  pretty (CovLoc file l1 l2 c1 c2) =
    mconcat [ pretty file, ":", pretty l1, ",", pretty c1, "-",  pretty l2, ",", pretty c2]

data CoverageAnnotation = CoverLocation CovLoc
                        | CoverBool CovLoc Bool
                        deriving (Ord, Eq, Show, Read, Generic, Serialise)
                        deriving Flat via (AsSerialize CoverageAnnotation)

instance Pretty CoverageAnnotation where
  pretty (CoverLocation loc) = pretty loc
  pretty (CoverBool loc b)   = pretty b <> " at " <> pretty loc

-- | This type keeps track of all coverage annotations and where they have been inserted / what
-- annotations are expected to be found when executing a piece of code.
newtype CoverageIndex = CoverageIndex { _coverageAnnotations :: Set CoverageAnnotation }
                      deriving (Ord, Eq, Show, Generic)
                      deriving newtype (Semigroup, Monoid, Serialise)
                      deriving Flat via (AsSerialize CoverageIndex)

makeLenses ''CoverageIndex

-- | Include a location coverage annotation in the index
addLocationToCoverageIndex :: MonadWriter CoverageIndex m => GHC.RealSrcSpan -> m CoverageAnnotation
addLocationToCoverageIndex src = do
  let ann = CoverLocation (toCovLoc src)
  tell . CoverageIndex $ Set.singleton ann
  return ann

-- | Include a boolean coverage annotation in the index
addBoolCaseToCoverageIndex :: MonadWriter CoverageIndex m => GHC.RealSrcSpan -> Bool -> m CoverageAnnotation
addBoolCaseToCoverageIndex src b = do
  let ann = boolCaseCoverageAnn src b
  tell . CoverageIndex $ Set.singleton ann
  return ann

boolCaseCoverageAnn :: GHC.RealSrcSpan -> Bool -> CoverageAnnotation
boolCaseCoverageAnn src b = CoverBool (toCovLoc src) b

-- | Obviously this function computes a GHC.RealSrcSpan from a CovLoc
toCovLoc :: GHC.RealSrcSpan -> CovLoc
toCovLoc sp = CovLoc (GHC.unpackFS $ GHC.srcSpanFile sp)
                     (GHC.srcSpanStartLine sp)
                     (GHC.srcSpanEndLine sp)
                     (GHC.srcSpanStartCol sp)
                     (GHC.srcSpanEndCol sp)
