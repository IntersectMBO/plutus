
module PlutusCore.Flat.Decoder.Run(strictDecoder,listTDecoder) where

import Control.Exception (Exception, try)
import Data.ByteString qualified as B
import Data.ByteString.Internal qualified as BS
import Foreign (Ptr, plusPtr, withForeignPtr)
import ListT (ListT (..))
import PlutusCore.Flat.Decoder.Prim (dBool)
import PlutusCore.Flat.Decoder.Types (DecodeException, Get (runGet), GetResult (..), S (S),
                                      tooMuchSpace)
import System.IO.Unsafe (unsafePerformIO)

-- | Given a decoder and an input buffer returns either the decoded value or an error (if the input buffer is not fully consumed)
strictDecoder :: Get a -> B.ByteString -> Int -> Either DecodeException a
strictDecoder get bs usedBits=
  strictDecoder_ get bs usedBits $ \(GetResult s'@(S ptr' o') a) endPtr ->
    if ptr' /= endPtr || o' /= 0
      then tooMuchSpace endPtr s'
      else return a

strictDecoder_ ::
     Exception e
  => Get a1
  -> BS.ByteString
  -> Int
  -> (GetResult a1 -> Ptr b -> IO a)
  -> Either e a
strictDecoder_ get (BS.PS base off len) usedBits check =
  unsafePerformIO . try $
  withForeignPtr base $ \base0 ->
    let ptr = base0 `plusPtr` off
        endPtr = ptr `plusPtr` len
     in do res <- runGet get endPtr (S ptr usedBits)
           check res endPtr
{-# NOINLINE strictDecoder_ #-}


-- strictRawDecoder :: Exception e => Get t -> B.ByteString -> Either e (t,B.ByteString, NumBits)
-- strictRawDecoder get (BS.PS base off len) = unsafePerformIO . try $
--   withForeignPtr base $ \base0 ->
--     let ptr = base0 `plusPtr` off
--         endPtr = ptr `plusPtr` len
--     in do
--       GetResult (S ptr' o') a <- runGet get endPtr (S ptr 0)
--       return (a, BS.PS base (ptr' `minusPtr` base0) (endPtr `minusPtr` ptr'), o')

{-|
Decode a list of values, one value at a time.

Useful in case that the decoded values takes a lot more memory than the encoded ones.

See <../test/Big.hs> for a test and an example of use.

See also "Flat.AsBin".

@since 0.5
-}
listTDecoder :: Get a -> BS.ByteString -> IO (ListT IO a)
listTDecoder get (BS.PS base off len) =
    withForeignPtr base $ \base0 -> do
        let ptr = base0 `plusPtr` off
            endPtr = ptr `plusPtr` len
            s = S ptr 0
            go s = do
                GetResult s' b <- runGet dBool endPtr s
                if b
                    then do
                        GetResult s'' a <- runGet get endPtr s'
                        return $ Just (a, ListT $ go s'')
                    else return Nothing
        return $ ListT (go s)
