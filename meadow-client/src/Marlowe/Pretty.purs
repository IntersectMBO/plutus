module Marlowe.Pretty where

import Prelude

import Data.Array (uncons)
import Data.Foldable (foldl)
import Data.Generic.Rep
  ( class Generic
  , Argument(..)
  , Constructor(..)
  , NoArguments
  , NoConstructors
  , Product(..)
  , Sum(..)
  , from
  )
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Monoid (mempty)
import Data.String (Pattern(..), charAt, contains, length)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)
import Text.PrettyPrint.Leijen
  ( Doc
      ( Empty
      )
  , appendWithLine
  , comma
  , encloseSep
  , hang
  , lbracket
  , parens
  , rbracket
  , text
  , (<+>)
  )
import Type.Data.Boolean (kind Boolean)

class Pretty a where
  pretty :: a -> Doc

class GenericPrettyArgs a where
  genericPrettyArgs' :: a -> Array Doc

instance genericPrettyNoConstructors :: Pretty NoConstructors where
  pretty a = mempty

instance genericPrettyArgsNoArguments :: GenericPrettyArgs NoArguments where
  genericPrettyArgs' _ = []

instance genericPrettySum :: (Pretty a, Pretty b) => Pretty (Sum a b) where
  pretty (Inl a) = pretty a
  pretty (Inr b) = pretty b

instance genericPrettyArgsProduct ::
  ( GenericPrettyArgs a
  , GenericPrettyArgs b
  ) =>
  GenericPrettyArgs (Product a b) where
  genericPrettyArgs' (Product a b) = genericPrettyArgs' a <> genericPrettyArgs' b

instance genericPrettyConstructor ::
  ( GenericPrettyArgs a
  , IsSymbol name
  ) =>
  Pretty (Constructor name a) where
  pretty (Constructor a) = case genericPrettyArgs' a of
    args -> case uncons args of
      Just { head: x, tail: [] } -> hang ((length ctor) + 1) (text ctor <+> (parens' x))
      Just { head: x, tail: xs } -> hang ((length ctor) + 1) (text ctor <+> (parens' x) `appendWithLine'` (foldl (\a b ->
        (appendWithLine' a (parens' b))) mempty xs))
      Nothing -> text ctor
    where
    ctor ::
      String
    ctor = reflectSymbol (SProxy :: SProxy name)
    parens' ::
      Doc ->
      Doc
    parens' Empty = Empty
    parens' d
      | surroundedByParens (show d) = d
      | contains (Pattern " ") (show d) = parens d
      | otherwise = d
    appendWithLine' ::
      Doc ->
      Doc ->
      Doc
    appendWithLine' Empty d = d
    appendWithLine' d Empty = d
    appendWithLine' a b = appendWithLine a b

surroundedByParens :: String -> Boolean
surroundedByParens s = fromMaybe false do
  pre <- charAt 0 s
  suf <- charAt (length s - 1) s
  pure $ pre == '(' && suf == ')'

instance genericPrettyArgsArgument ::
  ( Pretty a
  ) =>
  GenericPrettyArgs (Argument a) where
  genericPrettyArgs' (Argument a) = [pretty a]

instance genericPrettyString :: Pretty String where
  pretty a = text (show a)

instance genericPrettyInt :: Pretty Int where
  pretty a = text (show a)

instance prettyArray :: (Pretty a, Show a) => Pretty (Array a) where
  pretty a = encloseSep lbracket rbracket comma (map pretty a)

genericPretty :: forall a rep. Generic a rep => Pretty rep => a -> Doc
genericPretty x = pretty (from x)
