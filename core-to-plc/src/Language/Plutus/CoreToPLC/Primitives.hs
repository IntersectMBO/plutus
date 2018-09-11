-- | Primitive names that correspond to Plutus Core primitives.
module Language.Plutus.CoreToPLC.Primitives where

import           Language.Plutus.CoreToPLC.Error

import           GHC.Natural
import qualified Language.PlutusCore             as PC

-- | An abstract data type representing bytestrings in Plutus Core.
data ByteString

haskellIntSize :: Natural
haskellIntSize = 64

haskellBSSize :: Natural
haskellBSSize = 64

instSize :: Natural -> PC.Term tyname name () -> PC.Term tyname name ()
instSize n t = PC.TyInst () t (PC.TyInt () n)

appSize :: Natural -> PC.Type tyname () -> PC.Type tyname ()
appSize n t = PC.TyApp () t (PC.TyInt () n)

mkConstant :: PC.BuiltinName -> PC.Term tyname name ()
mkConstant n = PC.Constant () $ PC.BuiltinName () n

-- TODO: resizing primitives? better handling of sizes?

concatenate :: ByteString -> ByteString -> ByteString
concatenate = mustBeReplaced

takeByteString :: Int -> ByteString -> ByteString
takeByteString = mustBeReplaced

dropByteString :: Int -> ByteString -> ByteString
dropByteString = mustBeReplaced

sha2_256 :: ByteString -> ByteString
sha2_256 = mustBeReplaced

sha3_256 :: ByteString -> ByteString
sha3_256 = mustBeReplaced

verifySignature :: ByteString -> ByteString -> ByteString -> Bool
verifySignature = mustBeReplaced

equalsByteString :: ByteString -> ByteString -> Bool
equalsByteString = mustBeReplaced

txhash :: ByteString
txhash = mustBeReplaced

blocknum :: Int
blocknum = mustBeReplaced

error :: a
error = mustBeReplaced
