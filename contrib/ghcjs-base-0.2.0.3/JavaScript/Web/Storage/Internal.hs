{-# LANGUAGE DeriveDataTypeable #-}

module JavaScript.Web.Storage.Internal where

import GHCJS.Types

import Data.Typeable

newtype Storage      = Storage JSVal deriving Typeable
newtype StorageEvent = StorageEvent JSVal deriving Typeable
