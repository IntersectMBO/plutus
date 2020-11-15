{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports    #-}

module Codec ( Codec(..)
             , Tm
             , flatCodec
             , cborCodec
             , withZlib
             , withPureZlib
             , codecs
             ) where

import qualified Data.ByteString                    as BS
import qualified Data.ByteString.Lazy               as LBS
import           Data.Text                          (Text)

import           Language.PlutusCore                (DefaultFun (..))
import           Language.PlutusCore.Universe
import           Language.UntypedPlutusCore

import           "pure-zlib" Codec.Compression.Zlib as PureZlib
import           "zlib" Codec.Compression.Zlib      as Zlib
import           Codec.Serialise                    (Serialise, deserialise, serialise)
import           Flat                               (Flat, flat, unflat)

type Tm a = Term a DefaultUni DefaultFun ()

data Codec a = Codec
  { serialize   :: a -> BS.ByteString
  , deserialize :: BS.ByteString -> a
  }

fromDecoded :: Show error => Either error a -> a
fromDecoded (Left err) = error $ show err
fromDecoded (Right  v) = v

flatCodec :: Flat a => Codec (Tm a)
flatCodec = Codec
  { serialize   = flat
  , deserialize = fromDecoded . unflat
  }

cborCodec :: Serialise a => Codec (Tm a)
cborCodec = Codec
  { serialize   = LBS.toStrict . serialise
  , deserialize = deserialise . LBS.fromStrict
  }

withZlib :: Codec a -> Codec a
withZlib codec = Codec
  { serialize = LBS.toStrict . Zlib.compress . LBS.fromStrict . serialize codec
  , deserialize = (deserialize codec) . LBS.toStrict . Zlib.decompress . LBS.fromStrict
  }

withPureZlib :: Codec a -> Codec a
withPureZlib codec = Codec
  { serialize = serialize (withZlib codec)
  , deserialize = (deserialize codec) . LBS.toStrict . fromDecoded . PureZlib.decompress . LBS.fromStrict
  }

codecs    :: (Flat a, Serialise a) => [ (Text, Codec (Tm a)) ]
codecs    =
  [ ("flat", flatCodec)
  , ("flat-zlib", withZlib flatCodec)
  , ("flat-pure-zlib", withPureZlib flatCodec)
  , ("cbor", cborCodec)
  , ("cbor-zlib", withZlib cborCodec)
  , ("cbor-pure-zlib", withPureZlib cborCodec)
  ]
