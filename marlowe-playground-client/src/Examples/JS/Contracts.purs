module Examples.JS.Contracts where

example :: String
example =
  """
const contract : Contract = Close
"""

escrow :: String
escrow =
  """
/* Parties */
const alice : Party = Role("alice");
const bob : Party = Role("bob");
const carol : Party = Role("carol");

/* Value under escrow */
const price : SomeNumber = 450n;

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

const pay : [Bound]    = [Bound(0n, 0n)];
const refund : [Bound] = [Bound(1n, 1n)];
const both : [Bound]   = [Bound(0n, 1n)];

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
                                   100n, Close);

/* The contract to follow when Alice and Bob have made the same choice. */

const agreement : Contract = If(ValueEQ(aliceChosen, 0n),
                                Pay(alice, Party(bob), ada, price, Close),
                                Close);

/* Inner part of contract */

const inner : Contract = When([Case(aliceChoice,
                          When([Case(bobChoice,
                                     If(ValueEQ(aliceChosen, bobChosen),
                                        agreement,
                                        arbitrate))],
                                60n, arbitrate))],
                          40n, Close);

/* What does the vanilla contract look like?
  - if Alice and Bob choose
      - and agree: do it
      - and disagree: Carol decides
  - Carol also decides if timeout after one choice has been made;
  - refund if no choices are made. */

const contract : Contract = When([Case(Deposit(alice, alice, ada, price), inner)],
                                 10n,
                                 Close)
"""

zeroCouponBond :: String
zeroCouponBond =
  """
const investor : Party = Role("investor");
const issuer : Party = Role("issuer");

const contract : Contract = When([Case(
                                    Deposit(investor, investor, ada, 850n),
                                    Pay(investor, Party(issuer), ada, 850n,
                                        When([ Case(Deposit(investor, issuer, ada, 1000n),
                                                    Pay(investor, Party(investor), ada, 1000n, Close))
                                             ],
                                             20n,
                                             Close)
                                       ))],
                                  10n,
                                  Close);
"""

couponBondGuaranteed :: String
couponBondGuaranteed =
  """
const issuer : Party = Role("issuer");
const guarantor : Party = Role("guarantor");
const investor : Party = Role("investor");

const contract : Contract = When([
                                Case(Deposit(investor, guarantor, ada, 1030n),
                                    When([
                                        Case(Deposit(investor, investor, ada, 1000n),
                                            Pay(investor, Party(issuer), ada, 1000n,
                                                When([
                                                    Case(Deposit(investor, issuer, ada, 10n),
                                                        Pay(investor, Party(investor), ada, 10n,
                                                            Pay(investor, Party(guarantor), ada, 10n,
                                                                When([
                                                                    Case(Deposit(investor, issuer, ada, 10n),
                                                                        Pay(investor, Party(investor), ada, 10n,
                                                                            Pay(investor, Party(guarantor), ada, 10n,
                                                                                When([
                                                                                    Case(Deposit(investor, issuer, ada, 1010n),
                                                                                            Pay(investor, Party(investor), ada, 1010n,
                                                                                                Pay(investor, Party(guarantor), ada, 1010n, Close)
                                                                                            )
                                                                                        )
                                                                                        ], 20n, Close)
                                                                                )
                                                                            )
                                                                        )
                                                                    ], 15n, Close)
                                                                )
                                                            )
                                                        )
                                                    ], 10n, Close)
                                                )
                                            )
                                        ], 5n, Close)
                                    )
                                ], 5n, Close)
"""

swap :: String
swap =
  """
const lovelacePerAda : SomeNumber = 1000000n;
const amountOfAda : SomeNumber = 1000n;
const amountOfLovelace : SomeNumber = lovelacePerAda * amountOfAda;
const amountOfDollars : SomeNumber = 100n;

const dollars : Token = Token("85bb65", "dollar")

type SwapParty = {
 party: Party;
 currency: Token;
 amount: SomeNumber;
};

const alice : SwapParty = {
   party: Role("alice"),
   currency: ada,
   amount: amountOfLovelace
}

const bob : SwapParty = {
   party: Role("bob"),
   currency: dollars,
   amount: amountOfDollars
}

const makeDeposit = function(src : SwapParty, timeout : SomeNumber,
                             continuation : Contract) : Contract
{
   return When([Case(Deposit(src.party, src.party, src.currency, src.amount),
                     continuation)],
               timeout,
               Close);
}

const makePayment = function(src : SwapParty, dest : SwapParty,
                             continuation : Contract) : Contract
{
   return Pay(src.party, Party(dest.party), src.currency, src.amount,
              continuation);
}

const contract : Contract = makeDeposit(alice, 10n,
                               makeDeposit(bob, 20n,
                                   makePayment(alice, bob,
                                       makePayment(bob, alice,
                                           Close))))
"""

cfd :: String
cfd =
  """

const party : Party = Role("party")

const counterParty = Role("counterparty")

const oracle: Party = Role("oracle")

function waitForEvent (action : Action, timeout : SomeNumber,  alternative : Contract): (_: Contract) => Contract {
    return cont => When([Case(action, cont)], timeout, alternative)
} 

function before(time: SomeNumber): SomeNumber {
    return time
}    
function orElse(contract: Contract): Contract {
    return contract
}

function receiveValue(val: string): Action {
    return Choice(ChoiceId(val, oracle), [Bound(0, 100)])
}

function readValue(val : string): Value {
    return ChoiceValue(ChoiceId(val, oracle))
}

function waitFor(delay: SomeNumber): (_: Contract) => Contract {
    return cont => When([], delay, cont)
}

function checkIf(obs: Observation, c1: Contract, c2: Contract): Contract {
    return If(obs, c1, c2)
}

function thenDo(c: Contract): Contract {
    return c
}

function elseDo(c: Contract): Contract {
    return c
}


function letValue(name: string, v: Value): (_: Contract) => Contract {
    return cont => Let (ValueId(name), v, cont)
}

function useValue(name: string): Value {
    return UseValue(name)
}

function value(v: SomeNumber): Value {
    return Constant(v)
}

function fromParty(a: AccountId): AccountId {
    return a
}

function toParty(p: Party): Payee {
    return Party(p)
} 

function withToken(tkn: Token): Token {
    return tkn
}

const end: Contract = Close

function amountOf(amount: Value): Value {
    return amount
}

function minus(v1: Value, v2: Value): Value {
    return SubValue(v1, v2)
}

function sendPayment(fromParty: Party, toCounterParty: Payee, tkn: Token, payoff: Value): (_: Contract) => Contract {
    return cont => Pay(fromParty, toCounterParty, tkn, payoff, cont)
}

function Do(actions: Array<(_: Contract) => Contract>, last: Contract): Contract {
    const foldRight = <A, B>(xs: Array<A>, zero: B) => (f: (b: B, a: A) => B): B => {
        const len = xs.length;
        if (len === 0) return zero;
        else {
            const last = xs[len - 1];
            const inits = xs.slice(0, len - 1);
            return foldRight(inits, f(zero, last))(f);
        }
    }
    return foldRight(actions, last)((b, a) => a(b))
}

const contract = (() => {
    const partyCollateralToken = Token("", "")
    const partyCollateralAmount = value(1000n)
    const counterPartyCollateralToken = Token("", "")
    const counterPartyCollateralAmount = value(1000n)
    const endDate = 1000n
    const partyCollateralDeposit = Deposit(party, party, partyCollateralToken, partyCollateralAmount)

    const counterPartyCollateralDeposit = Deposit(counterParty, counterParty, counterPartyCollateralToken, counterPartyCollateralAmount)


    const minValue = (val1: Value, val2: Value) => Cond(ValueGE(val1, val2), val2, val1)

    return Do([
        waitForEvent(partyCollateralDeposit, before(100n), orElse(end)),
        waitForEvent(counterPartyCollateralDeposit, before(100n), orElse(end)),
        waitForEvent(receiveValue("price1"), before(100n), orElse(end)),
        waitFor(endDate),
        waitForEvent(receiveValue("price2"), before(endDate + 100n), orElse(end)),
        letValue("delta", minus(readValue("price1"), readValue("price2")))
    ],  checkIf(ValueEQ(useValue("delta"), value(0)), 
            thenDo(end),
            elseDo(
                checkIf(ValueLT(useValue("delta"), value(0)),
                    thenDo(
                        Do([
                            letValue("absdelta", minus(value(0), useValue("delta"))),
                            (() => {
                                const payoff = minValue(useValue("absdelta"), partyCollateralAmount)
                                return sendPayment(fromParty(party), toParty(counterParty), withToken(partyCollateralToken), amountOf(payoff))
                            })()
                        ], end)
                    ),
                    elseDo(
                        Do([
                            (() => {
                                const payoff = minValue(useValue("delta"), partyCollateralAmount)
                                return sendPayment(fromParty(party), toParty(counterParty), withToken(partyCollateralToken), amountOf(payoff))
                            })()
                        ], end)
                    )
                )
            )
        )
    )
})()

"""
