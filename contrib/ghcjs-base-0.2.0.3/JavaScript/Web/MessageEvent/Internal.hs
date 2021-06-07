{-# LANGUAGE DeriveDataTypeable #-}

module JavaScript.Web.MessageEvent.Internal where

import Data.Typeable

import GHCJS.Types

newtype MessageEvent = MessageEvent JSVal deriving (Typeable)
