module PlutusBenchmark.NoFib.Knights.Queue
  ( Queue, createQueue, addFront, addBack,
    addAllFront, addAllBack, inquireFront,
    inquireBack, removeFront, removeBack,
    emptyQueue
  ) where

import PlutusTx.Prelude as Tx

type Queue a = [a]

createQueue :: Queue a
createQueue = []
{-# INLINABLE createQueue #-}

addFront :: a -> Queue a -> Queue a
addFront x q = x:q
{-# INLINABLE addFront #-}

addBack :: a -> Queue a -> Queue a
addBack x q = q Tx.++ [x]
{-# INLINABLE addBack #-}

addAllFront :: [a] -> Queue a -> Queue a
addAllFront list q = list Tx.++ q
{-# INLINABLE addAllFront #-}

addAllBack :: [a] -> Queue a -> Queue a
addAllBack list q = q Tx.++ list
{-# INLINABLE addAllBack #-}

inquireFront :: Queue a -> a
inquireFront []    = Tx.error ()
{-# INLINABLE inquireFront #-}

inquireFront (h:_) = h

inquireBack :: Queue a -> a
inquireBack []     = Tx.error ()
inquireBack [x]    = x
inquireBack (_:xs) = inquireBack xs
{-# INLINABLE inquireBack #-}

removeFront :: Queue a -> Queue a
removeFront []    = Tx.error ()
removeFront (_:t) = t
{-# INLINABLE removeFront #-}

removeBack :: Queue a -> Queue a
removeBack []     = Tx.error ()
removeBack [_]    =  []
removeBack (x:xs) = x:(removeBack xs)
{-# INLINABLE removeBack #-}

emptyQueue :: Queue a -> Bool
emptyQueue [] = True
emptyQueue _  = False
{-# INLINABLE emptyQueue #-}


{-
sizeQueue :: Queue b -> Integer
sizeQueue xs = length' xs
-}
{-# INLINABLE sizeQueue #-}
