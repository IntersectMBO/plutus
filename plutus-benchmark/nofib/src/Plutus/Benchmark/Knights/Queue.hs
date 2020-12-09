module Plutus.Benchmark.Knights.Queue
  ( Queue, createQueue, addFront, addBack,
    addAllFront, addAllBack, inquireFront,
    inquireBack, removeFront, removeBack,
    emptyQueue
  ) where

import           PlutusTx.Prelude as Tx

type Queue a = [a]

{-# NOINLINE createQueue #-}
createQueue :: Queue a
createQueue = []

{-# NOINLINE addFront #-}
addFront :: a -> Queue a -> Queue a
addFront x q = x:q

{-# NOINLINE addBack #-}
addBack :: a -> Queue a -> Queue a
addBack x q = q Tx.++ [x]

{-# NOINLINE addAllFront #-}
addAllFront :: [a] -> Queue a -> Queue a
addAllFront list q = list Tx.++ q

{-# NOINLINE addAllBack #-}
addAllBack :: [a] -> Queue a -> Queue a
addAllBack list q = q Tx.++ list

{-# NOINLINE inquireFront #-}
inquireFront :: Queue a -> a
inquireFront []    = Tx.error ()

inquireFront (h:_) = h

{-# NOINLINE inquireBack #-}
inquireBack :: Queue a -> a
inquireBack []     = Tx.error ()
inquireBack [x]    = x
inquireBack (_:xs) = inquireBack xs

{-# NOINLINE removeFront #-}
removeFront :: Queue a -> Queue a
removeFront []    = Tx.error ()
removeFront (_:t) = t

{-# NOINLINE removeBack #-}
removeBack :: Queue a -> Queue a
removeBack []     = Tx.error ()
removeBack [_]    =  []
removeBack (x:xs) = x:(removeBack xs)

{-# NOINLINE emptyQueue #-}
emptyQueue :: Queue a -> Bool
emptyQueue [] = True
emptyQueue _  = False


{-
{-# NOINLINE sizeQueue #-}
sizeQueue :: Queue b -> Integer
sizeQueue xs = length' xs
-}
