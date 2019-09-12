{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators     #-}
module Language.Marlowe.Pretty (pretty, Pretty, prettyFragment) where

import           Data.Text               (Text)
import qualified Data.Text               as Text
import           GHC.Generics            ((:*:) ((:*:)), (:+:) (L1, R1), C, Constructor, D, Generic, K1 (K1), M1 (M1),
                                          Rep, S, U1, conName, from)
import           Text.PrettyPrint.Leijen (Doc, comma, encloseSep, hang, lbracket, line, lparen, parens, rbracket,
                                          rparen, space, text)

-- | This function will pretty print an a but will not wrap the whole
-- expression in parentheses or add an initial newline, where as for
-- technical reasons, @prettyFragment@ will.
--
-- >>> prettyFragment $ MyData One (MyData One Two)
-- (MyData One (MyData One Two))
--
-- >>> pretty $ MyData One (MyData One Two)
-- MyData One (MyData One Two)
pretty :: (Generic a, Pretty1 (Rep a)) => a -> Doc
pretty a = pretty1 True $ from a

class Pretty a where
  prettyFragment :: a -> Doc
  default prettyFragment :: (Generic a, (Pretty1 (Rep a))) => a -> Doc
  prettyFragment = pretty1 False . from

class Pretty1 f where
  pretty1 :: Bool -> f x -> Doc
  isNullary :: f x -> Bool

instance Pretty1 U1 where
  pretty1 _ _ = mempty
  isNullary _ = True

instance (Pretty1 f) => Pretty1 (M1 D c f) where
    pretty1 topLevel (M1 a) = pretty1 topLevel a
    isNullary (M1 a) = isNullary a

instance (Constructor c, Pretty1 f) => Pretty1 (M1 C c f) where
    pretty1 topLevel c@(M1 a) = line' . parens' $ hang 2 $ text (conName c) <> pretty1 False a
        where
            parens' f = if topLevel || isNullary a then f else parens f
            line' f = if topLevel || isNullary a then f else line <> f
    isNullary (M1 a) = isNullary a

instance (Pretty1 f) => Pretty1 (M1 S c f) where
    pretty1 _ (M1 a) = space' (pretty1 False a)
        where
          -- FIXME: unfortunately I can't work out how to get rid of trailing spaces without showing
          space' f = case show f of
            ('\n':_) -> f
            _        -> space <> f
    isNullary (M1 a) = isNullary a

instance Pretty f => Pretty1 (K1 t f) where
    pretty1 _ (K1 a) = prettyFragment a
    isNullary _ = False

instance (Pretty1 a, Pretty1 b) => Pretty1 (a :+: b) where
    pretty1 topLevel (L1 a) = pretty1 topLevel a
    pretty1 topLevel (R1 a) = pretty1 topLevel a
    isNullary (R1 a) = isNullary a
    isNullary (L1 a) = isNullary a

instance (Pretty1 a, Pretty1 b) => Pretty1 (a :*: b) where
    pretty1 topLevel (f :*: g) = pretty1 topLevel f <> pretty1 topLevel g
    isNullary _ = False

instance Pretty String where
  prettyFragment = text

instance Pretty Text where
  prettyFragment = text . show . Text.unpack

instance Pretty Int where
  prettyFragment = text . show

instance Pretty Integer where
  prettyFragment = text . show

instance (Pretty a, Pretty b) => Pretty (a, b) where
  prettyFragment (a, b) = encloseSep lparen rparen (comma <> space) [prettyFragment a, prettyFragment b]

instance (Pretty a) => Pretty [a] where
  prettyFragment a = encloseSep lbracket rbracket comma (map prettyFragment a)
