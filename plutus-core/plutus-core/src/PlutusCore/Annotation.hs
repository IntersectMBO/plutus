{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeFamilies   #-}
-- GHC 8.10 wans about the derived MonoFoldable instance, GHC>=9.2 works fine
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
module PlutusCore.Annotation
    ( Ann (..)
    , SrcSpan (..)
    , SrcSpans (..)
    , InlineHints (..)
    , Inline (..)
    , annAlwaysInline
    , annMayInline
    , Megaparsec.SourcePos (..)
    , Megaparsec.Pos
    , addSrcSpan
    , lineInSrcSpan
    ) where

import Control.DeepSeq
import Data.List qualified as List
import Data.MonoTraversable
import Data.Semigroup (Any (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Flat (Flat (..))
import GHC.Generics
import Prettyprinter
import Text.Megaparsec.Pos as Megaparsec

newtype InlineHints name a = InlineHints { shouldInline :: a -> name -> Bool }
    deriving (Semigroup, Monoid) via (a -> name -> Any)

instance Show (InlineHints name a) where
    show _ = "<inline hints>"

-- | An annotation type used during the compilation.
data Ann = Ann
    { annInline   :: Inline
    , annSrcSpans :: SrcSpans
    }
    deriving stock (Eq, Ord, Generic, Show)

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
    | MayInline
    deriving stock (Eq, Ord, Generic, Show)

instance Pretty Ann where
    pretty = viaShow

-- | Create an `Ann` with `AlwaysInline`.
annAlwaysInline :: Ann
annAlwaysInline = Ann{annInline = AlwaysInline, annSrcSpans = mempty}

-- | Create an `Ann` with `MayInline`.
annMayInline :: Ann
annMayInline = Ann{annInline = MayInline, annSrcSpans = mempty}


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
    deriving anyclass (Flat, NFData)

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
    deriving newtype (Eq, Ord, Semigroup, Monoid, MonoFoldable, NFData)
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
addSrcSpan s (Ann i (SrcSpans ss)) = Ann i (SrcSpans $ Set.insert s ss)

-- | Tells if a line (positive integer) falls inside a SrcSpan.
lineInSrcSpan :: Pos -> SrcSpan -> Bool
lineInSrcSpan pos spn =
    let i = Megaparsec.unPos pos
    in i >= srcSpanSLine spn && i <= srcSpanELine spn
