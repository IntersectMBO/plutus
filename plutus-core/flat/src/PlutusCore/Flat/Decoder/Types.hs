{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}

-- | Strict Decoder Types
module PlutusCore.Flat.Decoder.Types
  ( Get (..)
  , S (..)
  , GetResult (..)
  , Decoded
  , DecodeException (..)
  , notEnoughSpace
  , tooMuchSpace
  , badEncoding
  , badOp
  ) where

import Control.DeepSeq (NFData (..))
import Control.Exception (Exception, throwIO)
import Data.Word (Word8)
import Foreign (Ptr)

#if MIN_VERSION_base(4,9,0)
import Control.Monad.Fail qualified as Fail
#endif

{-|
A decoder.

Given:

* end of input buffer

* current position in input buffer

Returns:

* decoded value

* new position in input buffer -}
newtype Get a
  = Get
  { runGet
      :: Ptr Word8
      -> S
      -> IO (GetResult a)
  }

-- Seems to give better performance than the derived version
instance Functor Get where
  fmap f g =
    Get $ \end s -> do
      GetResult s' a <- runGet g end s
      return $ GetResult s' (f a)
  {-# INLINE fmap #-}

-- Is this correct?
instance NFData (Get a) where
  rnf !_ = ()

instance Show (Get a) where
  show _ = "Get"

instance Applicative Get where
  pure x = Get (\_ ptr -> return $ GetResult ptr x)
  {-# INLINE pure #-}
  Get f <*> Get g =
    Get $ \end ptr1 -> do
      GetResult ptr2 f' <- f end ptr1
      GetResult ptr3 g' <- g end ptr2
      return $ GetResult ptr3 (f' g')
  {-# INLINE (<*>) #-}
  Get f *> Get g =
    Get $ \end ptr1 -> do
      GetResult ptr2 _ <- f end ptr1
      g end ptr2
  {-# INLINE (*>) #-}

instance Monad Get where
  return = pure
  {-# INLINE return #-}
  (>>) = (*>)
  {-# INLINE (>>) #-}
  Get x >>= f =
    Get $ \end s -> do
      GetResult s' x' <- x end s
      runGet (f x') end s'
  {-# INLINE (>>=) #-}
#if !(MIN_VERSION_base(4,13,0))
  fail = failGet
#endif

#if MIN_VERSION_base(4,9,0)
instance Fail.MonadFail Get where
  fail = failGet
#endif
{-# INLINE failGet #-}
failGet :: String -> Get a
failGet msg = Get $ \end s -> badEncoding end s msg

-- | Decoder state
data S
  = S
  { currPtr :: {-# UNPACK #-} !(Ptr Word8)
  , usedBits :: {-# UNPACK #-} !Int
  }
  deriving (Show, Eq, Ord)

data GetResult a
  = GetResult {-# UNPACK #-} !S !a
  deriving (Functor)

-- | A decoded value
type Decoded a = Either DecodeException a

-- | An exception during decoding
data DecodeException
  = NotEnoughSpace Env
  | TooMuchSpace Env
  | BadEncoding Env String
  | BadOp String
  deriving (Show, Eq, Ord)

type Env = (Ptr Word8, S)

notEnoughSpace :: Ptr Word8 -> S -> IO a
notEnoughSpace endPtr s = throwIO $ NotEnoughSpace (endPtr, s)

tooMuchSpace :: Ptr Word8 -> S -> IO a
tooMuchSpace endPtr s = throwIO $ TooMuchSpace (endPtr, s)

badEncoding :: Ptr Word8 -> S -> String -> IO a
badEncoding endPtr s msg = throwIO $ BadEncoding (endPtr, s) msg

badOp :: String -> IO a
badOp msg = throwIO $ BadOp msg

instance Exception DecodeException
