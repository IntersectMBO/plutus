{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators              #-}
{-# OPTIONS_GHC -fno-warn-orphans       #-}
module Language.Marlowe.Pretty where

import qualified Data.ByteString.Lazy    as BSL
import           Data.Text               (Text)
import qualified Data.Text               as Text
import           GHC.Generics            ((:*:) ((:*:)), (:+:) (L1, R1), C, Constructor, D, Generic, K1 (K1), M1 (M1),
                                          Rep, S, U1, conName, from)
import           Ledger                  (PubKey (..), PubKeyHash (..), Slot (..))
import           Ledger.Ada              (Ada, getLovelace)
import           Ledger.Value
import           LedgerBytes
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
pretty a = pretty1 True $ GHC.Generics.from a

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


{- This is temp ugly hack to not break Marlowe Playground.

    In PureScript we use String to represent a PubKey,
    and Integer to represent Slot.

    During Analisys, Marlowe Playground PureScript pretty prints a contract,
    and sends a String to backend, which 'read' a contract, and analyses it.

    That's why we require @Haskell.read . PureScript.pretty == id@

    Currently, Marlowe Playground saves a Haskell contract to a file,
    and runs Haskell interpreter. A script usually pretty prints a contract
    to standard output, and that's get returned to the Playground as
    a Haskell compiled contract. It's parsed by PureScript.

    Thus, we require @PureScript.parse . Haskell.pretty == id

    These two requirements break @Haskell.read . Haskell.show == id@

 -}

instance Pretty Slot where
    prettyFragment (Slot n) = prettyFragment n

instance Pretty PubKey where
    prettyFragment (PubKey (LedgerBytes lb)) = prettyFragment lb

instance Pretty PubKeyHash where
    prettyFragment (PubKeyHash bs) = prettyFragment bs

instance Read PubKey where
    readsPrec p x = [(PubKey (LedgerBytes v), s) | (v, s) <- readsPrec p x]

instance Read PubKeyHash where
    readsPrec p x = [(PubKeyHash bs, s) | (bs, s) <- readsPrec p x]

instance Read Slot where
    readsPrec p x = [(Slot v, s) | (v, s) <- readsPrec p x]

instance Pretty BSL.ByteString where
    prettyFragment = text . show . BSL.toStrict


instance Pretty Ada where
    prettyFragment x = prettyFragment (getLovelace x)

instance Read CurrencySymbol where
    readsPrec p x = [(CurrencySymbol v, s) | (v, s) <- readsPrec p x]

instance Read TokenName where
    readsPrec p x = [(TokenName v, s) | (v, s) <- readsPrec p x]

deriving instance Pretty CurrencySymbol
deriving instance Pretty TokenName
