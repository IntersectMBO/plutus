{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators     #-}
module Language.Marlowe.Pretty (pretty, Pretty, prettyFragment) where

import           GHC.Generics            ((:*:) ((:*:)), (:+:) (L1, R1), C, Constructor, D, Generic, K1 (K1), M1 (M1),
                                          Rep, S, U1, conName, from)
import           Prelude                 hiding ((<$>))
import           Text.PrettyPrint.Leijen (Doc, comma, encloseSep, hang, lbracket, parens, rbracket, space, text, (<$>))

-- | This function will pretty print an a but will not wrap the whole
-- expression in parentheses, where as @prettyFragment@ will.
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
    pretty1 topLevel c@(M1 a) = parens' $ hang 2 $ text (conName c) <> pretty1 False a
        where
            parens' f = if topLevel || isNullary a then f else parens f
    isNullary (M1 a) = isNullary a

instance (Pretty1 f) => Pretty1 (M1 S c f) where
    pretty1 _ (M1 a) = space <> pretty1 False a
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
    pretty1 topLevel (f :*: g) = pretty1 topLevel f `split` pretty1 topLevel g
        where
            -- FIXME: horrible hack, it seems that `isNullary g` always returns False so instead
            -- we manually prettyprint it and check if it is surrounded with parens
            split a b = case (show . pretty1 topLevel) g of
                (' ':'(':_) -> a <$> b
                _           -> a <> b
    isNullary _ = False

instance Pretty String where
  prettyFragment = text

instance Pretty Int where
  prettyFragment = text . show

instance Pretty Integer where
  prettyFragment = text . show

instance (Pretty a, Pretty b) => Pretty (a, b)

instance (Pretty a) => Pretty [a] where
  prettyFragment a = encloseSep lbracket rbracket comma (map prettyFragment a)
