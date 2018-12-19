module Language.Marlowe.Escrow where

import           Language.Marlowe.Common
import           Language.Marlowe.Compiler
import           Wallet.API                     ( PubKey(..) )

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

alice :: Person
alice = PubKey 1

bob :: Person
bob = PubKey 2

carol :: Person
carol = PubKey 3

escrowContract :: Contract
escrowContract = CommitCash iCC1 alice
                    (Value 450)
                    10 100
                    (When (OrObs (twoChose alice bob carol 0)
                                 (twoChose alice bob carol 1))
                          90
                          (Choice (twoChose alice bob carol 1)
                                  (Pay iP1 alice bob
                                       (Committed iCC1)
                                       100
                                       Null)
                                  redeemOriginal)
                          redeemOriginal)
                    Null

chose :: Person -> ConcreteChoice -> Observation
chose per@(PubKey i) c = PersonChoseThis (IdentChoice i) per c

oneChose :: Person -> Person -> ConcreteChoice -> Observation
oneChose per per' val =
        (OrObs (chose per val) (chose per' val))

twoChose :: Person -> Person -> Person -> ConcreteChoice -> Observation
twoChose p1 p2 p3 c =
        OrObs (AndObs (chose p1 c) (oneChose p2 p3 c))
              (AndObs (chose p2 c) (chose p3 c))

redeemOriginal :: Contract
redeemOriginal = RedeemCC iCC1 Null

iCC1 :: IdentCC
iCC1 = IdentCC 1

iP1 :: IdentPay
iP1 = IdentPay 1
