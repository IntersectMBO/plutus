module BasicContract where

import           Marlowe

{-# ANN module "HLint: ignore" #-}

main :: IO ()
main = putStrLn $ show contract

-------------------------------------
-- Write your code below this line --
-------------------------------------

-- Escrow example using embedding

contract :: Contract
contract = Commit 1 iCC1 alice
                  (Constant 450)
                  10 100
                  (When (OrObs (majority_chose refund)
                               (majority_chose pay))
                        90
                        (Choice (majority_chose pay)
                                (Pay 2 iCC1 bob
                                     (Committed iCC1)
                                     100
                                     Null
                                     Null) 
                                (redeem_original 3))
                       (redeem_original 4))
                  Null
    where majority_chose = two_chose alice bob carol

-- Participants

alice, bob, carol :: Person
alice = 1
bob = 2
carol = 3

-- Possible votes

refund, pay :: Choice
refund = 0
pay = 1

-- Vote counting

chose :: Integer -> Choice -> Observation
chose per c = ChoseThis (1, per) c

one_chose :: Person -> Person -> Choice -> Observation
one_chose per per' val = (OrObs (chose per val) (chose per' val))

two_chose :: Person -> Person -> Person -> Choice -> Observation
two_chose p1 p2 p3 c = OrObs (AndObs (chose p1 c) (one_chose p2 p3 c))
                             (AndObs (chose p2 c) (chose p3 c))

-- Redeem alias

redeem_original :: Integer -> Contract
redeem_original x = Pay x iCC1 alice (Committed iCC1) 100 Null Null

-- Commit identifier

iCC1 :: IdCommit
iCC1 = 1


