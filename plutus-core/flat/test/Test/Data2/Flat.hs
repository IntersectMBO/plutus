module Test.Data2.Flat (module Test.Data2) where

import PlutusCore.Flat
import PlutusCore.Flat.Decoder.Prim (dBool)
import PlutusCore.Flat.Encoder (eFalse, eTrue)
import Test.Data2

instance Flat a => Flat (List a) where
  encode (Cons2 x xs) = eFalse <> encode x <> encode xs
  encode Nil2 = eTrue
  decode = do
    tag <- dBool
    if tag then pure Nil2 else Cons2 <$> decode <*> decode
  size (Cons2 x xs) n = 1 + size x (size xs n)
  size Nil2 n = 1 + n
