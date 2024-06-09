{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators         #-}
-- | Pretty-printing in a Show-like format, used for dumping ASTs for the
-- coq certifier (plutus-cert)
module Text.SimpleShow
  ( SimpleShow (..)
  , parens
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS (unpack)
import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set, toList)
import Data.Some.Newtype
import Data.Text (Text, pack)
import GHC.Generics
import GHC.Word
import Numeric.Natural


parens :: Bool -> Text -> Text
parens True x  = "(" <> x <> ")"
parens False x = x

-- | Used to determine if a constructor is applied to any arguments, if so, it
-- will need parentheses when printing
class GIsApplied f where
  gIsApplied :: f a -> Bool

instance GIsApplied U1 where
  gIsApplied _ = False

instance GIsApplied V1 where
  gIsApplied _ = False

instance GIsApplied (K1 i c) where
  gIsApplied _ = True

instance (GIsApplied f) => GIsApplied (M1 D c f) where
  gIsApplied (M1 x) = gIsApplied x

instance (GIsApplied f) => GIsApplied (M1 C c f) where
  gIsApplied (M1 x) = gIsApplied x

instance (GIsApplied f) => GIsApplied (M1 S c f) where
  gIsApplied (M1 x) = gIsApplied x

instance GIsApplied (f :*: g) where
  gIsApplied _ = True

instance (GIsApplied f, GIsApplied g) => GIsApplied (f :+: g) where
  gIsApplied (L1 x) = gIsApplied x
  gIsApplied (R1 x) = gIsApplied x



class SimpleShow a where
  simpleShow :: a -> Text

  default simpleShow :: (Generic a, SimpleShow' (Rep a)) => a -> Text
  simpleShow x = simpleShow' (from x)

class SimpleShow' f where
  simpleShow' :: f a -> Text

instance SimpleShow' U1 where
  simpleShow' U1 = ""

instance (SimpleShow' f, SimpleShow' g) => SimpleShow' (f :*: g) where
  simpleShow' (x :*: y) = simpleShow' x <> " " <> simpleShow' y

instance (SimpleShow' f, SimpleShow' g) => SimpleShow' (f :+: g) where
  simpleShow' (L1 x) = simpleShow' x
  simpleShow' (R1 x) = simpleShow' x

instance (SimpleShow' f) => SimpleShow' (M1 D c f) where
  simpleShow' (M1 x) = simpleShow' x

instance (SimpleShow' f, Constructor c, GIsApplied f) => SimpleShow' (M1 C c f) where
  simpleShow' m@(M1 x)
    | gIsApplied x = parens True $ pack (conName m) <> " " <> simpleShow' x
    | otherwise = pack (conName m)

instance (SimpleShow' f) => SimpleShow' (M1 S s f) where
  -- Ignore selector names
  simpleShow' (M1 x) = simpleShow' x

instance (SimpleShow a) => SimpleShow' (K1 i a) where
  simpleShow' (K1 x) = simpleShow x


instance SimpleShow Char where
  simpleShow = pack . show

instance SimpleShow Int where
  simpleShow = pack . show

instance SimpleShow Integer where
  simpleShow = pack . show

instance SimpleShow ByteString where
  simpleShow = simpleShow . BS.unpack

instance SimpleShow Bool where
  simpleShow = pack . show

instance (forall a. SimpleShow (f a)) => SimpleShow (Some f) where
  simpleShow (Some x) = parens True ("Some " <>  (simpleShow x))

instance SimpleShow Double where
  simpleShow = pack . show

instance SimpleShow Text where
  simpleShow = pack . show

instance SimpleShow (GHC.Word.Word64) where
  simpleShow = pack . show

instance SimpleShow (GHC.Word.Word8) where
  simpleShow x = parens True ("Word8 " <> (pack (show x)))

instance SimpleShow a => SimpleShow (Set a) where
  simpleShow x = parens True ("Set " <> simpleShow (toList x))

instance (SimpleShow a, SimpleShow b) => SimpleShow (a, b) where
  simpleShow (a, b) = "(" <> simpleShow a <> ", " <> simpleShow b <> ")"


instance SimpleShow a => SimpleShow [a]

instance
  ( SimpleShow a
  , SimpleShow b
  , SimpleShow c
  , SimpleShow d
  , SimpleShow e
  )
  => SimpleShow (a, b, c, d, e)

deriving anyclass instance SimpleShow a => SimpleShow (NonEmpty a)
deriving anyclass instance SimpleShow ()
instance SimpleShow Natural where
  simpleShow = pack . show
