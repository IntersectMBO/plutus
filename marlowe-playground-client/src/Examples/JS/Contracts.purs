module Examples.JS.Contracts where

escrow :: String
escrow =
  """/* Parties */
const alice = role("alice");
const bob = role("bob");
const carol = role("carol");

/* Accounts */
const alicesAccount = accountId(bigInt(0), alice);

/* Value under escrow */
const price = constant(bigInt(450));

/* helper function to build Actions */

const choiceName = "choice";

const choiceIdBy = function (party) {
                       return choiceId(choiceName, party);
                   }

const choiceBy = function(party, bounds) {
                      return choice(choiceIdBy(party), bounds);
                  };


const choiceValueBy = function(party) {
                          return choiceValue(choiceIdBy(party));
                      };

/* Names for choices */

const pay    = [bound(bigInt(0), bigInt(0))];
const refund = [bound(bigInt(1), bigInt(1))];
const both   = [bound(bigInt(0), bigInt(1))];

/* Name choices according to person making choice and choice made */

const alicePay    = choiceBy(alice, pay);
const aliceRefund = choiceBy(alice, refund);
const aliceChoice = choiceBy(alice, both);

const bobPay    = choiceBy(bob, pay);
const bobRefund = choiceBy(bob, refund);
const bobChoice = choiceBy(bob, both);

const carolPay    = choiceBy(carol, pay);
const carolRefund = choiceBy(carol, refund);
const carolChoice = choiceBy(carol, both);

/* the values chosen in choices */

const aliceChosen = choiceValueBy(alice);
const bobChosen = choiceValueBy(bob);

/* The contract to follow when Alice and Bob disagree, or if
   Carol has to intervene after a single choice from Alice or Bob. */

const arbitrate = whenM([caseM(carolRefund, closeM),
                         caseM(carolPay, payM(alicesAccount, bob, ada, price, closeM))],
                        bigInt(100), closeM);

/* The contract to follow when Alice and Bob have made the same choice. */

const agreement = ifM(valueEQ(aliceChosen, constant(bigInt(0))),
                      payM(alicesAccount, bob, ada, price, closeM),
                      closeM);

/* Inner part of contract */

const inner = whenM([caseM(aliceChoice,
                whenM([caseM(bobChoice,
                             ifM(valueEQ(aliceChosen, bobChosen),
                               agreement,
                               arbitrate))],
                      bigInt(60), arbitrate))],
                bigInt(40), closeM);

/* What does the vanilla contract look like?
  - if Alice and Bob choose
      - and agree: do it
      - and disagree: Carol decides
  - Carol also decides if timeout after one choice has been made;
  - refund if no choices are made. */

const contract = whenM([caseM(deposit(alicesAccount, alice, ada, price), inner)],
                       bigInt(10),
                       closeM)

contract
"""

zeroCouponBond :: String
zeroCouponBond =
  """const investor = role("investor");
const issuer = role("issuer");

const investorAcc = accountId(bigInt(0), investor);

whenM([caseM(
        deposit(investorAcc, investor, ada, constant(bigInt(850))),
        payM(investorAcc, issuer, ada, constant(bigInt(850)),
             whenM([ caseM(deposit(investorAcc, issuer, ada, constant(bigInt(1000))),
                           payM(investorAcc, investor, ada, constant(bigInt(1000)), closeM))
                   ],
                   bigInt(20),
                   closeM)
            ))],
      bigInt(10),
      closeM);
"""

couponBondGuaranteed :: String
couponBondGuaranteed =
  """const issuer = role("issuer");
const guarantor = role("guarantor");
const investor = role("investor");
const investorAcc = accountId(bigInt(0), investor);

whenM([caseM(deposit(investorAcc, guarantor, ada, constant(bigInt(1030))),
        (whenM([caseM(deposit(investorAcc, investor, ada, constant(bigInt(1000))),
                payM(investorAcc, issuer, ada, constant(bigInt(1000)),
                    (whenM([caseM(deposit( investorAcc, issuer, ada, constant(bigInt(10))),
                            payM(investorAcc, investor, ada, constant(bigInt(10)),
                                payM(investorAcc, guarantor, ada, constant(bigInt(10)),
                                    (whenM([caseM(deposit(investorAcc, issuer, ada, constant(bigInt(10))),
                                            payM(investorAcc, investor, ada, constant(bigInt(10)),
                                                payM(investorAcc, guarantor, ada, constant(bigInt(10)),
                                                    (whenM([caseM(deposit(investorAcc, issuer, ada, constant(bigInt(1010))),
                                                            payM(investorAcc, investor, ada, constant(bigInt(1010)),
                                                                payM(investorAcc, guarantor, ada, constant(bigInt(1010)), closeM)
                                                            ))], bigInt(20), closeM)
                                                    )       
                                                )   
                                            ))], bigInt(15), closeM)
                                    )       
                                )   
                            ))], bigInt(10), closeM)
                    )       
                ))], bigInt(5), closeM)
        ))], bigInt(5), closeM)
"""

swap :: String
swap =
  """const party1 = role("party1");
const party2 = role("party2");
const gracePeriod = bigInt(5);
const date1 = bigInt(20);
const acc1 = accountId(bigInt(1), party1);
const acc2 = accountId(bigInt(2), party2);

const contract = whenM([ caseM(deposit(acc1, party1, ada, constant(bigInt(500))),
                           /* when 1st party committed, wait for 2nd */
                           whenM([caseM(deposit(acc2, party2, ada, constant(bigInt(300))),
                                       payM(acc1, party2, ada, constant(bigInt(500)),
                                           payM(acc2, party1, ada, constant(bigInt(300)), closeM)))
                               ], date1,
                           /* if a party dosn't commit, simply Close to the owner */
                           closeM))
                       ], date1.minus(gracePeriod), closeM);

contract
"""
