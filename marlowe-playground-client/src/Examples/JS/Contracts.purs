module Examples.JS.Contracts where

escrow :: String
escrow =
  """/* Parties */
const alice : Party = role("alice");
const bob : Party = role("bob");
const carol : Party = role("carol");

/* Accounts */
const alicesAccount : AccountId = accountId(0, alice);

/* Value under escrow */
const price : SomeNumber = new bignumber.BigNumber(450);

/* helper function to build Actions */

const choiceName : string = "choice";

const choiceIdBy = function (party : Party) : ChoiceId {
                       return choiceId(choiceName, party);
                   }

const choiceBy = function(party : Party, bounds : [Bound]) : Action {
                      return choice(choiceIdBy(party), bounds);
                  };


const choiceValueBy = function(party : Party) : Value {
                          return choiceValue(choiceIdBy(party));
                      };

/* Names for choices */

const pay : [Bound]    = [bound(0, 0)];
const refund : [Bound] = [bound(1, 1)];
const both : [Bound]   = [bound(0, 1)];

/* Name choices according to person making choice and choice made */

const alicePay : Action    = choiceBy(alice, pay);
const aliceRefund : Action = choiceBy(alice, refund);
const aliceChoice : Action = choiceBy(alice, both);

const bobPay : Action    = choiceBy(bob, pay);
const bobRefund : Action = choiceBy(bob, refund);
const bobChoice : Action = choiceBy(bob, both);

const carolPay : Action    = choiceBy(carol, pay);
const carolRefund : Action = choiceBy(carol, refund);
const carolChoice : Action = choiceBy(carol, both);

/* the values chosen in choices */

const aliceChosen : Value = choiceValueBy(alice);
const bobChosen : Value = choiceValueBy(bob);

/* The contract to follow when Alice and Bob disagree, or if
   Carol has to intervene after a single choice from Alice or Bob. */

const arbitrate : Contract = whenM([caseM(carolRefund, closeM),
                                    caseM(carolPay, payM(alicesAccount, bob, ada, price, closeM))],
                                   100, closeM);

/* The contract to follow when Alice and Bob have made the same choice. */

const agreement : Contract = ifM(valueEQ(aliceChosen, 0),
                                 payM(alicesAccount, bob, ada, price, closeM),
                                 closeM);

/* Inner part of contract */

const inner : Contract = whenM([caseM(aliceChoice,
                           whenM([caseM(bobChoice,
                                        ifM(valueEQ(aliceChosen, bobChosen),
                                          agreement,
                                          arbitrate))],
                                 60, arbitrate))],
                           40, closeM);

/* What does the vanilla contract look like?
  - if Alice and Bob choose
      - and agree: do it
      - and disagree: Carol decides
  - Carol also decides if timeout after one choice has been made;
  - refund if no choices are made. */

const contract : Contract = whenM([caseM(deposit(alicesAccount, alice, ada, price), inner)],
                                  10,
                                  closeM)

contract
"""

zeroCouponBond :: String
zeroCouponBond =
  """const investor : Party = role("investor");
const issuer : Party = role("issuer");

const investorAcc : AccountId = accountId(0, investor);

whenM([caseM(
        deposit(investorAcc, investor, ada, 850),
        payM(investorAcc, issuer, ada, 850,
             whenM([ caseM(deposit(investorAcc, issuer, ada, 1000),
                           payM(investorAcc, investor, ada, 1000, closeM))
                   ],
                   20,
                   closeM)
            ))],
      10,
      closeM);
"""

couponBondGuaranteed :: String
couponBondGuaranteed =
  """const issuer : Party = role("issuer");
const guarantor : Party = role("guarantor");
const investor : Party = role("investor");
const investorAcc : AccountId = accountId(0, investor);

whenM([caseM(deposit(investorAcc, guarantor, ada, 1030),
        (whenM([caseM(deposit(investorAcc, investor, ada, 1000),
                payM(investorAcc, issuer, ada, 1000,
                    (whenM([caseM(deposit( investorAcc, issuer, ada, 10),
                            payM(investorAcc, investor, ada, 10,
                                payM(investorAcc, guarantor, ada, 10,
                                    (whenM([caseM(deposit(investorAcc, issuer, ada, 10),
                                            payM(investorAcc, investor, ada, 10,
                                                payM(investorAcc, guarantor, ada, 10,
                                                    (whenM([caseM(deposit(investorAcc, issuer, ada, 1010),
                                                            payM(investorAcc, investor, ada, 1010,
                                                                payM(investorAcc, guarantor, ada, 1010, closeM)
                                                            ))], 20, closeM)
                                                    )
                                                )
                                            ))], 15, closeM)
                                    )
                                )
                            ))], 10, closeM)
                    )
                ))], 5, closeM)
        ))], 5, closeM)
"""

swap :: String
swap =
  """const party1 : Party = role("party1");
const party2 : Party = role("party2");
const gracePeriod : SomeNumber = new bignumber.BigNumber(5);
const date1 : SomeNumber = new bignumber.BigNumber(20);
const acc1 : AccountId = accountId(1, party1);
const acc2 : AccountId = accountId(2, party2);

const contract : Contract = whenM([ caseM(deposit(acc1, party1, ada, 500),
                                      /* when 1st party committed, wait for 2nd */
                                      whenM([caseM(deposit(acc2, party2, ada, 300),
                                                  payM(acc1, party2, ada, 500,
                                                      payM(acc2, party1, ada, 300, closeM)))
                                          ], date1,
                                      /* if a party dosn't commit, simply Close to the owner */
                                      closeM))
                                  ], date1.minus(gracePeriod), closeM);

contract
"""
