module Examples.JS.Contracts where

escrow :: String
escrow =
  """/* Parties */
var alice = role("alice");
var bob = role("bob");
var carol = role("carol");

/* Accounts */
var alicesAccount = accountId(bigInt(0), alice);

/* Value under escrow */
var price = constant(bigInt(450));

/* helper function to build Actions */

var choiceName = "choice";

var choiceIdBy = function (party) {
                     return choiceId(choiceName, party);
                 }

var choiceBy = function(party, bounds) {
                    return choice(choiceIdBy(party), bounds);
                };


var choiceValueBy = function(party) {
                        return choiceValue(choiceIdBy(party));
                    };

/* Names for choices */

var pay    = [bound(bigInt(0), bigInt(0))];
var refund = [bound(bigInt(1), bigInt(1))];
var both   = [bound(bigInt(0), bigInt(1))];

/* Name choices according to person making choice and choice made */

var alicePay    = choiceBy(alice, pay);
var aliceRefund = choiceBy(alice, refund);
var aliceChoice = choiceBy(alice, both);

var bobPay    = choiceBy(bob, pay);
var bobRefund = choiceBy(bob, refund);
var bobChoice = choiceBy(bob, both);

var carolPay    = choiceBy(carol, pay);
var carolRefund = choiceBy(carol, refund);
var carolChoice = choiceBy(carol, both);

/* the values chosen in choices */

var aliceChosen = choiceValueBy(alice);
var bobChosen = choiceValueBy(bob);

/* The contract to follow when Alice and Bob disagree, or if
   Carol has to intervene after a single choice from Alice or Bob. */

var arbitrate = whenM([caseM(carolRefund, close),
                       caseM(carolPay, payM(alicesAccount, bob, ada, price, close))],
                      bigInt(100), close);

/* The contract to follow when Alice and Bob have made the same choice. */

var agreement = ifM(valueEQ(aliceChosen, constant(bigInt(0))),
                    payM(alicesAccount, bob, ada, price, close),
                    close);

/* Inner part of contract */

var inner = whenM([caseM(aliceChoice,
              whenM([caseM(bobChoice,
                           ifM(valueEQ(aliceChosen, bobChosen),
                             agreement,
                             arbitrate))],
                    bigInt(60), arbitrate))],
              bigInt(40), close);

/* What does the vanilla contract look like?
  - if Alice and Bob choose
      - and agree: do it
      - and disagree: Carol decides
  - Carol also decides if timeout after one choice has been made;
  - refund if no choices are made. */

var contract = whenM([caseM(deposit(alicesAccount, alice, ada, price), inner)],
                     bigInt(10),
                     close)

contract
"""

zeroCouponBond :: String
zeroCouponBond =
  """var investor = role("investor");
var issuer = role("issuer");

var investorAcc = accountId(bigInt(0), investor);

whenM([caseM(
        deposit(investorAcc, investor, ada, constant(bigInt(850))),
        payM(investorAcc, issuer, ada, constant(bigInt(850)),
             whenM([ caseM(deposit(investorAcc, issuer, ada, constant(bigInt(1000))),
                           payM(investorAcc, investor, ada, constant(bigInt(1000)), close))
                   ],
                   bigInt(20),
                   close)
            ))],
      bigInt(10),
      close);
"""

couponBondGuaranteed :: String
couponBondGuaranteed =
  """var issuer = role("issuer");
var guarantor = role("guarantor");
var investor = role("investor");
var investorAcc = accountId(bigInt(0), investor);

whenM([caseM(deposit(investorAcc, guarantor, ada, bigInt(1030)),
        (whenM([caseM(deposit(investorAcc, investor, ada, bigInt(1000)),
                payM(investorAcc, issuer, ada, bigInt(1000),
                    (whenM([caseM(deposit( investorAcc, issuer, ada, bigInt(10)),
                            payM(investorAcc, investor, ada, bigInt(10),
                                payM(investorAcc, guarantor, ada, bigInt(10),
                                    (whenM([caseM(deposit(investorAcc, issuer, ada, bigInt(10)),
                                            payM(investorAcc, investor, ada, bigInt(10),
                                                payM(investorAcc, guarantor, ada, bigInt(10),
                                                    (whenM([caseM(deposit(investorAcc, issuer, ada, bigInt(1010)),
                                                            payM(investorAcc, investor, ada, bigInt(1010),
                                                                payM(investorAcc, guarantor, ada, bigInt(1010), close)
                                                            ))], bigInt(20), close)
                                                    )       
                                                )   
                                            ))], bigInt(15), close)
                                    )       
                                )   
                            ))], bigInt(10), close)
                    )       
                ))], bigInt(5), close)
        ))], bigInt(5), close)
"""

swap :: String
swap =
  """var party1 = role("party1");
var party2 = role("party2");
var gracePeriod = bigInt(5);
var date1 = bigInt(20);
var acc1 = accountId(bigInt(1), party1);
var acc2 = accountId(bigInt(2), party2);

var contract = whenM([ caseM(deposit(acc1, party1, ada, constant(bigInt(500))),
                         /* when 1st party committed, wait for 2nd */
                         whenM([caseM(deposit(acc2, party2, ada, constant(bigInt(300))),
                                     payM(acc1, party2, ada, constant(bigInt(500)),
                                         payM(acc2, party1, ada, constant(bigInt(300)), close)))
                             ], date1,
                         /* if a party dosn't commit, simply Close to the owner */
                         close))
                     ], date1.minus(gracePeriod), close);

contract
"""
