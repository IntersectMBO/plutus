module BasicContract where

import           Marlowe

{-# ANN module "HLint: ignore" #-}

main :: IO ()
main = putStrLn $ prettyPrintContract contract

-------------------------------------
-- Write your code below this line --
-------------------------------------

-- Escrow example using embedding

contract :: Contract
contract = CommitCash iCC1 alice
                      (ConstMoney 450)
                      10 100
                      (When (OrObs (majority_chose refund)
                                   (majority_chose pay))
                            90
                            (Choice (majority_chose pay)
                                    (Pay iP1 alice bob
                                         (AvailableMoney iCC1)
                                         100
                                         redeem_original)
                                    redeem_original)
                            redeem_original)
                      Null
    where majority_chose = two_chose alice bob carol

-- Participants

alice, bob, carol :: Person
alice = 1
bob = 2
carol = 3

-- Possible votes

refund, pay :: ConcreteChoice
refund = 0
pay = 1

-- Vote counting

chose :: Int -> ConcreteChoice -> Observation
chose per c = PersonChoseThis (IdentChoice per) per c

one_chose :: Person -> Person -> ConcreteChoice -> Observation
one_chose per per' val = (OrObs (chose per val) (chose per' val))

two_chose :: Person -> Person -> Person -> ConcreteChoice -> Observation
two_chose p1 p2 p3 c = OrObs (AndObs (chose p1 c) (one_chose p2 p3 c))
                             (AndObs (chose p2 c) (chose p3 c))

-- Redeem alias

redeem_original :: Contract
redeem_original = RedeemCC iCC1 Null

-- Commit identifier

iCC1 :: IdentCC
iCC1 = IdentCC 1

-- Payment identifier

iP1 :: IdentPay
iP1 = IdentPay 1


