# Marlowe ACTUS: standardised financial contracts on Cardano Computation Layer

_marlowe-actus_ is a library to generate Marlowe contracts from ACTUS contract terms

## ACTUS (algorithmic contract types unified standards)

ACTUS is a foundation that defines the ACTUS taxonomy of financial contracts, see https://www.actusfrf.org/

The following contract types are implemented in Haskell and Marlowe.

### Amortizing loans

An amortizing loan is a loan that requires periodic payments where a payment consists of the interest payment and the principal.

#### Principal at maturity (PAM)

Principal at maturity only defines periodic interest payments, the full principal is due at maturity.
A simple illustrative example of such a contract is the following

```
principal: 10000
interest rate: 2% p.a.
annual interest payments
term: 10 years
```

This generates yearly cash flows with the interest payment for 10 years and the principal repayment at maturity:

|Year|Balance|Principal|Interest|Payment|
|----|-------|---------|--------|-------|
|1|10000|0|200|200|
|2|10000|0|200|200|
|3|10000|0|200|200|
|4|10000|0|200|200|
|5|10000|0|200|200|
|6|10000|0|200|200|
|7|10000|0|200|200|
|8|10000|0|200|200|
|9|10000|0|200|200|
|10|10000|10000|200|10200|

The contract in ACTUS is specified as follows - only the relevant parameters are shown here:

```
ContractTerms
  { contractType = PAM
  , ct_IED       = iso8601ParseM "2020-01-01T00:00:00"
  , ct_MD        = iso8601ParseM "2030-01-01T00:00:00"
  , ct_NT        = Just 10000.0
  , ct_DCC       = Just DCC_E30_360
  , ct_IPCL      = Just $ Cycle 1 P_Y ShortStub False
  , ct_IPANX     = iso8601ParseM "2020-01-01T00:00:00"
  , ct_IPNR      = Just 0.02
  ...
  }
```

#### Linear Amortizer (LAM)

Regular principal repayments over time, the interest payments decrease linearly.

```
principal: 10000
principal repayment: 1000 p.a.
interest rate: 2% p.a.
annual interest payments
term: 10 years
```

|Year|Balance|Principal|Interest|Payment|
|----|-------|---------|--------|-------|
|1|10000|1000|200|1200|
|2|9000|1000|180|1180|
|3|8000|1000|160|1160|
|4|7000|1000|140|1140|
|5|6000|1000|120|1120|
|6|5000|1000|100|1100|
|7|4000|1000|80|1080|
|8|3000|1000|60|1060|
|9|2000|1000|40|1040|
|10|1000|1000|20|1020|

The contract in ACTUS is specified as follows - only the relevant parameters are shown here:

```
ContractTerms
  { contractType = LAM
  , ct_IED       = iso8601ParseM "2020-01-01T00:00:00"
  , ct_MD        = iso8601ParseM "2030-01-01T00:00:00"
  , ct_PRNXT     = Just 1000.0
  , ct_NT        = Just 10000.0
  , ct_DCC       = Just DCC_E30_360
  , ct_IPCL      = Just $ Cycle 1 P_Y ShortStub False
  , ct_IPANX     = iso8601ParseM "2020-01-01T00:00:00"
  , ct_IPNR      = Just 0.02
  , ct_IPAC      = Just 0.0
  , ct_PRCL      = Just $ Cycle 1 P_Y ShortStub False
  , ct_PRANX     = iso8601ParseM "2021-01-01T00:00:00"
  , ct_IPCB      = Just IPCB_NT
  ...
  }
```

#### Negative Amortizer (NAM)

Negative amortization means that the payments per period are smaller than the interest, i.e. the balance of the loan increases over time.

```
principal: 10000
interest rate: 2% p.a.
annual interest payments
term: 10 years
```

|Year|Balance|Principal|Interest|Payment|
|----|-------|---------|--------|-------|
|1|10000|1000|200|1000|
|2|9200|1000|184|1000|
|3|8384|1000|168|1000|
|4|7552|1000|151|1000|
|5|6703|1000|134|1000|
|6|5837|1000|117|1000|
|7|4954|1000|99|1000|
|8|4053|1000|81|1000|
|9|3134|1000|63|1000|
|10|2196|1000|44|1000|

The contract in ACTUS is specified as follows - only the relevant parameters are shown here:

```
ContractTerms
  { contractType = NAM
  , ct_IED       = iso8601ParseM "2020-01-01T00:00:00"
  , ct_MD        = iso8601ParseM "2030-01-01T00:00:00"
  , ct_PRNXT     = Just 1000.0
  , ct_NT        = Just 10000.0
  , ct_DCC       = Just DCC_E30_360
  , ct_IPCL      = Just $ Cycle 1 P_Y ShortStub False
  , ct_IPANX     = iso8601ParseM "2020-01-01T00:00:00"
  , ct_IPNR      = Just 0.02
  , ct_IPAC      = Just 0.0
  , ct_PRCL      = Just $ Cycle 1 P_Y ShortStub False
  , ct_PRANX     = iso8601ParseM "2021-01-01T00:00:00"
  , ct_IPCB      = Just IPCB_NT
  ...
  }
```

#### Annuity (ANN)

The annuity amortization consists of regular payments of equal amounts over the lifetime of the loan.

```
principal: 10000
interest rate: 2% p.a.
annual interest payments
term: 10 years
```

|Year|Balance|Principal|Interest|Payment|
|----|-------|---------|--------|-------|
|1|10000|800|200|1000|
|2|9200|816|184|1000|
|3|8384|832|168|1000|
|4|7552|849|151|1000|
|5|6703|866|134|1000|
|6|5837|883|117|1000|
|7|4954|901|99|1000|
|8|4053|919|81|1000|
|9|3134|937|63|1000|
|10|2196|956|44|1000|

The contract in ACTUS is specified as follows - only the relevant parameters are shown here:

```
ContractTerms
  { contractType = ANN
  , ct_IED       = iso8601ParseM "2020-01-01T00:00:00"
  , ct_MD        = iso8601ParseM "2030-01-01T00:00:00"
  , ct_PRNXT     = Just 1000.0
  , ct_NT        = Just 10000.0
  , ct_DCC       = Just DCC_E30_360
  , ct_IPCL      = Just $ Cycle 1 P_Y ShortStub False
  , ct_IPANX     = iso8601ParseM "2020-01-01T00:00:00"
  , ct_IPNR      = Just 0.02
  , ct_IPAC      = Just 0.0
  , ct_PRCL      = Just $ Cycle 1 P_Y ShortStub False
  , ct_PRANX     = iso8601ParseM "2021-01-01T00:00:00"
  , ct_IPCB      = Just IPCB_NT
  ...
  }
```

## Test cases

For the contract types mentioned above the implementation is tested with the test cases provided by ACTUS: https://github.com/actusfrf/actus-tests
