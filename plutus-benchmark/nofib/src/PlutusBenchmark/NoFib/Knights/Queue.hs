module PlutusBenchmark.NoFib.Knights.Queue
  ( Queue
  , createQueue
  , addFront
  , addBack
  , addAllFront
  , addAllBack
  , inquireFront
  , inquireBack
  , removeFront
  , removeBack
  , emptyQueue
  ) where

import PlutusTx.List qualified as List
import PlutusTx.Prelude as Tx

type Queue a = [a]

createQueue :: Queue a
createQueue = []
{-# INLINEABLE createQueue #-}

addFront :: a -> Queue a -> Queue a
addFront x q = x : q
{-# INLINEABLE addFront #-}

addBack :: a -> Queue a -> Queue a
addBack x q = q List.++ [x]
{-# INLINEABLE addBack #-}

addAllFront :: [a] -> Queue a -> Queue a
addAllFront list q = list List.++ q
{-# INLINEABLE addAllFront #-}

addAllBack :: [a] -> Queue a -> Queue a
addAllBack list q = q List.++ list
{-# INLINEABLE addAllBack #-}

inquireFront :: Queue a -> a
inquireFront [] = Tx.error ()
inquireFront (h : _) = h
{-# INLINEABLE inquireFront #-}

inquireBack :: Queue a -> a
inquireBack [] = Tx.error ()
inquireBack [x] = x
inquireBack (_ : xs) = inquireBack xs
{-# INLINEABLE inquireBack #-}

removeFront :: Queue a -> Queue a
removeFront [] = Tx.error ()
removeFront (_ : t) = t
{-# INLINEABLE removeFront #-}

removeBack :: Queue a -> Queue a
removeBack [] = Tx.error ()
removeBack [_] = []
removeBack (x : xs) = x : (removeBack xs)
{-# INLINEABLE removeBack #-}

emptyQueue :: Queue a -> Bool
emptyQueue [] = True
emptyQueue _ = False
{-# INLINEABLE emptyQueue #-}

{-
sizeQueue :: Queue b -> Integer
sizeQueue xs = length' xs
{-# INLINABLE sizeQueue #-}
-}
