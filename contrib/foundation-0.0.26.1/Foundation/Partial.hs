-- |
-- Module      : Foundation.Partial
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- Partial give a way to annotate your partial function with
-- a simple wrapper, which can only evaluated using 'fromPartial'
--
-- > fromPartial ( head [] )
--
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Foundation.Partial
    ( Partial
    , PartialError
    , partialError
    , partial
    , fromPartial
    , head
    , fromJust
    , fromLeft
    , fromRight
    ) where

import Basement.Compat.Base
import Basement.Compat.Identity

-- | Partialiality wrapper.
newtype Partial a = Partial (Identity a)
    deriving (Functor, Applicative, Monad)

-- | An error related to the evaluation of a Partial value that failed.
--
-- it contains the name of the function and the reason for failure
data PartialError = PartialError [Char] [Char]
    deriving (Show,Eq,Typeable)

instance Exception PartialError

-- | Throw an asynchronous PartialError
partialError :: [Char] -> [Char] -> a
partialError lbl exp = throw (PartialError lbl exp)

-- | Create a value that is partial. this can only be
-- unwrap using the 'fromPartial' function
partial :: a -> Partial a
partial = pure

-- | Dewrap a possible partial value
fromPartial :: Partial a -> a
fromPartial (Partial ida) = runIdentity ida

-- | Partial function to get the head of a list
head :: [a] -> Partial a
head l = partial $
    case l of
        []  -> partialError "head" "empty list"
        x:_ -> x

-- | Partial function to grab the value inside a Maybe
fromJust :: Maybe a -> Partial a
fromJust x = partial $
    case x of
        Nothing -> partialError "fromJust" "Nothing"
        Just y  -> y

-- Grab the Right value of an Either
fromRight :: Either a b -> Partial b
fromRight x = partial $
    case x of
        Left _ -> partialError "fromRight" "Left"
        Right a -> a

-- Grab the Left value of an Either
fromLeft :: Either a b -> Partial a
fromLeft x = partial $
    case x of
        Right _ -> partialError "fromLeft" "Right"
        Left a -> a
