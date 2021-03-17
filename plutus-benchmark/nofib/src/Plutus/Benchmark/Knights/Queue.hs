module Plutus.Benchmark.Knights.Queue
  ( Queue, createQueue, addFront, addBack,
    addAllFront, addAllBack, inquireFront,
    inquireBack, removeFront, removeBack,
    emptyQueue
  ) where

import           PlutusTx.Prelude as Tx

type Queue a = [a]

{-# INLINABLE createQueue #-}
createQueue :: Queue a
createQueue = []

{-# INLINABLE addFront #-}
addFront :: a -> Queue a -> Queue a
addFront x q = x:q

{-# INLINABLE addBack #-}
addBack :: a -> Queue a -> Queue a
addBack x q = q Tx.++ [x]

{-# INLINABLE addAllFront #-}
addAllFront :: [a] -> Queue a -> Queue a
addAllFront list q = list Tx.++ q

{-# INLINABLE addAllBack #-}
addAllBack :: [a] -> Queue a -> Queue a
addAllBack list q = q Tx.++ list

{-# INLINABLE inquireFront #-}
inquireFront :: Queue a -> a
inquireFront []    = Tx.error ()

inquireFront (h:_) = h

{-# INLINABLE inquireBack #-}
inquireBack :: Queue a -> a
inquireBack []     = Tx.error ()
inquireBack [x]    = x
inquireBack (_:xs) = inquireBack xs

{-# INLINABLE removeFront #-}
removeFront :: Queue a -> Queue a
removeFront []    = Tx.error ()
removeFront (_:t) = t

{-# INLINABLE removeBack #-}
removeBack :: Queue a -> Queue a
removeBack []     = Tx.error ()
removeBack [_]    =  []
removeBack (x:xs) = x:(removeBack xs)

{-# INLINABLE emptyQueue #-}
emptyQueue :: Queue a -> Bool
emptyQueue [] = True
emptyQueue _  = False


{-
{-# INLINABLE sizeQueue #-}
sizeQueue :: Queue b -> Integer
sizeQueue xs = length' xs
-}
