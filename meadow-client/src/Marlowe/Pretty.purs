module Marlowe.Pretty where

import Prelude

import Data.Generic.Rep (class Generic, Argument(..), Constructor(..), NoArguments, Product(..), Sum(..), from)
import Data.Monoid (mempty)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)
import Text.PrettyPrint.Leijen (Doc, hang, line, parens, space, text)
import Type.Data.Boolean (kind Boolean)

pretty :: forall a rep. Generic a rep => Pretty1 rep => a -> Doc
pretty x = pretty1 true (from x)

class Pretty a where
  prettyFragment :: a -> Doc

genericPretty :: forall a rep. Generic a rep => Pretty1 rep => a -> Doc
genericPretty x = pretty1 false (from x)

class Pretty1 f where
  pretty1 :: Boolean -> f -> Doc
  isNullary :: f -> Boolean

instance pretty1ArgsNoArguments :: Pretty1 NoArguments where
  pretty1 _ _ = mempty
  isNullary _ = true

instance pretty1Constructor :: (Pretty1 a, IsSymbol name) => Pretty1 (Constructor name a) where
  pretty1 topLevel (Constructor a) = line' $ parens' $ hang 2 $ text conName <> pretty1 false a
    where
      conName :: String
      conName = reflectSymbol (SProxy :: SProxy name)
      parens' f = if topLevel || isNullary a then f else parens f
      line' f = if topLevel || isNullary a then f else line <> f
  isNullary (Constructor a) = isNullary a

instance pretty1Argument :: (Pretty a) => Pretty1 (Argument a) where
  pretty1 topLevel (Argument a) = space <> prettyFragment a
  isNullary (Argument a) = false

instance pretty1Sum :: (Pretty1 l, Pretty1 r) => Pretty1 (Sum l r) where
  pretty1 topLevel (Inl l) = pretty1 topLevel l
  pretty1 topLevel (Inr r) = pretty1 topLevel r
  isNullary (Inl l) = isNullary l
  isNullary (Inr r) = isNullary r

instance pretty1Product :: (Pretty1 l, Pretty1 r) => Pretty1 (Product l r) where
  pretty1 topLevel (Product l r) = pretty1 topLevel l <> pretty1 topLevel r
  isNullary _ = false