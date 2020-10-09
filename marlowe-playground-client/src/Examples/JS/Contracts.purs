module Examples.JS.Contracts where

escrow :: String
escrow =
  """/* Parties */
const alice : Party = Role("alice");
const bob : Party = Role("bob");
const carol : Party = Role("carol");

/* Value under escrow */
const price : SomeNumber = new bignumber.BigNumber(450);

/* helper function to build Actions */

const choiceName : string = "choice";

const choiceIdBy = function (party : Party) : ChoiceId {
                       return ChoiceId(choiceName, party);
                   }

const choiceBy = function(party : Party, bounds : [Bound]) : Action {
                      return Choice(choiceIdBy(party), bounds);
                  };


const choiceValueBy = function(party : Party) : Value {
                          return ChoiceValue(choiceIdBy(party));
                      };

/* Names for choices */

const pay : [Bound]    = [Bound(0, 0)];
const refund : [Bound] = [Bound(1, 1)];
const both : [Bound]   = [Bound(0, 1)];

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

const arbitrate : Contract = When([Case(carolRefund, Close),
                                   Case(carolPay, Pay(alice, Party(bob), ada, price, Close))],
                                   100, Close);

/* The contract to follow when Alice and Bob have made the same choice. */

const agreement : Contract = If(ValueEQ(aliceChosen, 0),
                                Pay(alice, Party(bob), ada, price, Close),
                                Close);

/* Inner part of contract */

const inner : Contract = When([Case(aliceChoice,
                          When([Case(bobChoice,
                                     If(ValueEQ(aliceChosen, bobChosen),
                                        agreement,
                                        arbitrate))],
                                60, arbitrate))],
                          40, Close);

/* What does the vanilla contract look like?
  - if Alice and Bob choose
      - and agree: do it
      - and disagree: Carol decides
  - Carol also decides if timeout after one choice has been made;
  - refund if no choices are made. */

const contract : Contract = When([Case(Deposit(alice, alice, ada, price), inner)],
                                 10,
                                 Close)

contract

"""

zeroCouponBond :: String
zeroCouponBond =
  """const investor : Party = Role("investor");
const issuer : Party = Role("issuer");

When([Case(
        Deposit(investor, investor, ada, 850),
        Pay(investor, Party(issuer), ada, 850,
            When([ Case(Deposit(investor, issuer, ada, 1000),
                        Pay(investor, Party(investor), ada, 1000, Close))
                 ],
                 20,
                 Close)
           ))],
      10,
      Close);

"""

couponBondGuaranteed :: String
couponBondGuaranteed =
  """const issuer : Party = Role("issuer");
const guarantor : Party = Role("guarantor");
const investor : Party = Role("investor");

When([
    Case(Deposit(investor, guarantor, ada, 1030),
         When([
            Case(Deposit(investor, investor, ada, 1000),
                 Pay(investor, Party(issuer), ada, 1000,
                     When([
                         Case(Deposit(investor, issuer, ada, 10),
                              Pay(investor, Party(investor), ada, 10,
                                  Pay(investor, Party(guarantor), ada, 10,
                                      When([
                                          Case(Deposit(investor, issuer, ada, 10),
                                               Pay(investor, Party(investor), ada, 10,
                                                   Pay(investor, Party(guarantor), ada, 10,
                                                       When([
                                                           Case(Deposit(investor, issuer, ada, 1010),
                                                                Pay(investor, Party(investor), ada, 1010,
                                                                    Pay(investor, Party(guarantor), ada, 1010, Close)
                                                                   )
                                                               )
                                                            ], 20, Close)
                                                      )
                                                  )
                                              )
                                           ], 15, Close)
                                     )
                                 )
                             )
                          ], 10, Close)
                    )
                )
              ], 5, Close)
        )
     ], 5, Close)
"""

swap :: String
swap =
  """const party1 : Party = Role("party1");
const party2 : Party = Role("party2");
const gracePeriod : SomeNumber = new bignumber.BigNumber(5);
const date1 : SomeNumber = new bignumber.BigNumber(20);

const contract : Contract = When([ Case(Deposit(party1, party1, ada, 500),
                                     /* when 1st party committed, wait for 2nd */
                                     When([Case(Deposit(party2, party2, ada, 300),
                                                Pay(party1, Party(party2), ada, 500,
                                                    Pay(party2, Party(party1), ada, 300, Close)))
                                          ], date1,
                                     /* if a party dosn't commit, simply Close to the owner */
                                          Close))
                                 ], date1.minus(gracePeriod), Close);

contract
"""
