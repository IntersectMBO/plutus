{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeFamilies   #-}

module PlutusCore.Annotation
    ( Ann (..)
    , SrcSpan (..)
    , SrcSpans (..)
    , InlineHints (..)
    , Inline (..)
    , AnnInline (..)
    , Megaparsec.SourcePos (..)
    , Megaparsec.Pos
    , addSrcSpan
    , lineInSrcSpan
    ) where

import Control.DeepSeq
import Data.Default.Class
import Data.Hashable
import Data.List qualified as List
import Data.MonoTraversable
import Data.Set (Set)
import Data.Set qualified as Set
import GHC.Generics
import PlutusCore.Flat (Flat (..))
import Prettyprinter
import Text.Megaparsec.Pos as Megaparsec

newtype InlineHints name a = InlineHints { shouldInline :: a -> name -> Inline }

instance Show (InlineHints name a) where
    show _ = "<inline hints>"

instance Default (InlineHints name a) where
    def = InlineHints (\_ _ -> MayInline)

-- | An annotation type used during the compilation.
data Ann = Ann
    { annInline          :: Inline
    , annSrcSpans        :: SrcSpans
    , annIsAsDataMatcher :: Bool
    }
    deriving stock (Eq, Ord, Generic, Show)
    deriving anyclass (Hashable)

instance Default Ann where
  def =
    Ann
      { annInline = MayInline
      , annSrcSpans = mempty
      , annIsAsDataMatcher = False
      }

data Inline
    = -- | When calling @PlutusIR.Compiler.Definitions.defineTerm@ to add a new term definition,
      -- if we annotation the var on the LHS of the definition with `AlwaysInline`, the inliner will
      -- always inline that var.
      --
      -- This is currently used to ensure builtin functions such as @trace@ (when the @remove-trace@
      -- flag is on and @trace@ is rewritten to @const@) are inlined, because the inliner would
      -- otherwise not inline them. To achieve that, we annotate the definition with `AlwaysInline`
      -- when defining @trace@, i.e., @trace <AlwaysInline> = \_ a -> a@.
      AlwaysInline
    | -- | Signaling to the compiler that a binding is safe to inline. This is useful for
      -- annotating strict bindings that aren't obviously safe to inline.
      SafeToInline
    | MayInline
    deriving stock (Eq, Ord, Generic, Show)
    deriving anyclass (Hashable)

instance Pretty Ann where
    pretty = viaShow

class AnnInline a where
  -- | An annotation instructing the inliner to always inline a binding.
  annAlwaysInline :: a

  -- | An annotation signaling to the inliner that a binding is safe to inline.
  -- The inlining decision is left to the inliner. This is useful for
  -- annotating strict bindings that aren't obviously safe to inline.
  annSafeToInline :: a

  -- | An annotation that leaves the inlining decision to the inliner.
  annMayInline :: a

instance AnnInline () where
  annAlwaysInline = ()
  annSafeToInline = ()
  annMayInline = ()

instance AnnInline Ann where
    annAlwaysInline = def { annInline = AlwaysInline }
    annSafeToInline = def { annInline = SafeToInline }
    annMayInline = def { annInline = MayInline }

-- | The span between two source locations.
--
-- This corresponds roughly to the `SrcSpan` used by GHC,
-- but we define our own version so we don't have to depend on `ghc` to use it.
--
-- The line and column numbers are 1-based, and the unit is Unicode code point (or `Char`).
data SrcSpan = SrcSpan
    { srcSpanFile  :: FilePath
    , srcSpanSLine :: Int
    , srcSpanSCol  :: Int
    , srcSpanELine :: Int
    , srcSpanECol  :: Int
    -- ^ Same as GHC's @SrcSpan@, @srcSpanECol@ is usually one more than the column of
    -- the last character of the thing this @SrcSpan@ is for (unless the last character
    -- is the line break).
    }
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (Flat, Hashable, NFData)

instance Show SrcSpan where
    showsPrec _ s =
        showString (srcSpanFile s)
            . showChar ':'
            . showsPrec 0 (srcSpanSLine s)
            . showChar ':'
            . showsPrec 0 (srcSpanSCol s)
            . showChar '-'
            . showsPrec 0 (srcSpanELine s)
            . showChar ':'
            . showsPrec 0 (if srcSpanECol s == 0 then 0 else srcSpanECol s - 1)

instance Pretty SrcSpan where
    pretty = viaShow

newtype SrcSpans = SrcSpans {unSrcSpans :: Set SrcSpan}
    deriving newtype (Eq, Ord, Hashable, Semigroup, Monoid, MonoFoldable, NFData)
    deriving stock (Generic)
    deriving anyclass (Flat)

type instance Element SrcSpans = SrcSpan

instance Show SrcSpans where
    showsPrec _ (SrcSpans xs) =
        showString "{ "
            . showString
                ( case Set.toList xs of
                    [] -> "no-src-span"
                    ys -> List.intercalate ", " (show <$> ys)
                )
            . showString " }"

instance Pretty SrcSpans where
    pretty = viaShow

-- | Add an extra SrcSpan to existing 'SrcSpans' of 'Ann'
addSrcSpan :: SrcSpan -> Ann -> Ann
addSrcSpan s (Ann i (SrcSpans ss) b) = Ann i (SrcSpans $ Set.insert s ss) b

-- | Tells if a line (positive integer) falls inside a SrcSpan.
lineInSrcSpan :: Pos -> SrcSpan -> Bool
lineInSrcSpan pos spn =
    let i = Megaparsec.unPos pos
    in i >= srcSpanSLine spn && i <= srcSpanELine spn
