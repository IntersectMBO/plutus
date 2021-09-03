# Marlowe ACTUS: standardised financial contracts on Cardano Computation Layer

_marlowe-actus_ is a library to generate Marlowe contracts from ACTUS contract terms

## ACTUS (algorithmic contract types unified standards)

ACTUS is a foundation that defines the ACTUS taxonomy of financial contracts, see https://www.actusfrf.org/

### Contract types

The following contract types are implemented in Haskell and Marlowe.

#### Amortizing loans

An amortizing loan is a loan that requires periodic payments where a payment consists of the interest payment and the principal.

##### Principal at maturity (PAM)

Principal at maturity only defines periodic interest payments, the full principal is due at maturity.

##### Linear Amortizer (LAM)

Regular principal repayments over time, the interest payments decrease linearly.

##### Negative Amortizer (NAM)

Negative amortization means that the payments per period are smaller the interest, i.e. the balance of the loan increases over time.

##### Annuity (ANN)

The annuity amortization consists of regular payments of equal amounts over the lifetime of the loan.

## Test cases

For the contract types mentioned above the implementation is tested with the test cases provided by ACTUS: https://github.com/actusfrf/actus-tests
