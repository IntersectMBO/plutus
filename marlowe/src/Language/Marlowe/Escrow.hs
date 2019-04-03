module Language.Marlowe.Escrow where

import           Language.Marlowe
import           Ledger

{-
------------------------------------------
-- Implementation of an escrow contract --
------------------------------------------

   The contract allows person 1 to pay 450 ADA
   to person 2 by using person 3 as an escrow.

   Person 1 can commit 450 ADA until block 100.
   The payment will go through only if 2 out of the 3
   participants choose the number "1".

   If 2 out of the 3 participants chooses the number "0"
   or if payment did not go through after block 100,
   the money will be refunded to person 1.
-}

escrowContract :: Contract
escrowContract = CommitCash iCC1 alice
                    (Value 450)
                    10 100
                    (When (OrObs (twoChose aliceId alice bobId bob carolId carol 0)
                                 (twoChose aliceId alice bobId bob carolId carol 1))
                          90
                          (Choice (twoChose aliceId alice bobId bob carolId carol 1)
                                  (Pay iP1 alice bob
                                       (Committed iCC1)
                                       100
                                       Null)
                                  redeemOriginal)
                          redeemOriginal)
                    Null

chose :: IdentChoice -> Person -> ConcreteChoice -> Observation
chose = PersonChoseThis

oneChose :: IdentChoice -> Person -> IdentChoice -> Person -> ConcreteChoice -> Observation
oneChose ident per ident' per' val = OrObs (chose ident per val) (chose ident' per' val)

twoChose :: IdentChoice -> Person -> IdentChoice -> Person -> IdentChoice -> Person -> ConcreteChoice -> Observation
twoChose i1 p1 i2 p2 i3 p3 c =
        OrObs (AndObs (chose i1 p1 c) (oneChose i2 p2 i3 p3 c))
              (AndObs (chose i2 p2 c) (chose i3 p3 c))

redeemOriginal :: Contract
redeemOriginal = RedeemCC iCC1 Null

iCC1 :: IdentCC
iCC1 = IdentCC 1

iP1 :: IdentPay
iP1 = IdentPay 1

alice :: Person
alice = toPublicKey privateKey1

aliceId :: IdentChoice
aliceId = IdentChoice 1

bob :: Person
bob = toPublicKey privateKey2

bobId :: IdentChoice
bobId = IdentChoice 2

carol :: Person
carol = toPublicKey privateKey3

carolId :: IdentChoice
carolId = IdentChoice 3
