{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -O0 #-}
module Language.PlutusTx.Coordination.Contracts.Swap(
    Swap(..),
    swapValidator
    ) where

import qualified Language.PlutusTx            as PlutusTx
import           Ledger                       (Slot, PubKey, ValidatorScript (..), Value (..))
import qualified Ledger                       as Ledger
import           Ledger.Validation            (OracleValue (..), PendingTx (..), PendingTxIn (..), PendingTxOut (..))
import qualified Ledger.Validation            as Validation

import           Prelude                    (Bool (..), Eq (..), Int, Num (..), Ord (..))

data Ratio a = a :% a  deriving Eq

-- | A swap is an agreement to exchange cashflows at future dates. To keep
--  things simple, this is an interest rate swap (meaning that the cashflows are
--  interest payments on the same principal amount but with two different
--  interest rates, of which one is fixed and one is floating (varying with
--  time)) with only a single payment date.
--
--  At the beginning of the contract, the fixed rate is set to the expected
--  future value of the floating rate (so if the floating rate behaves as
--  expected, the two payments will be exactly equal).
--
data Swap = Swap
    { swapNotionalAmt     :: !Value
    , swapObservationTime :: !Slot
    , swapFixedRate       :: !(Ratio Int) -- ^ Interest rate fixed at the beginning of the contract
    , swapFloatingRate    :: !(Ratio Int) -- ^ Interest rate whose value will be observed (by an oracle) on the day of the payment
    , swapMargin          :: !Value -- ^ Margin deposited at the beginning of the contract to protect against default (one party failing to pay)
    , swapOracle          :: !PubKey -- ^ Public key of the oracle (see note [Oracles] in [[Language.PlutusTx.Coordination.Contracts]])
    }

-- | Identities of the parties involved in the swap. This will be the data
--   script which allows us to change the identities during the lifetime of
--   the contract (ie. if one of the parties sells their part of the contract)
--
--   In the future we could also put the `swapMargin` value in here to implement
--   a variable margin.
data SwapOwners = SwapOwners {
    swapOwnersFixedLeg :: !PubKey,
    swapOwnersFloating :: !PubKey
    }

type SwapOracle = OracleValue (Ratio Int)

-- | Validator script for the two transactions that initialise the swap.
--   See note [Swap Transactions]
--   See note [Contracts and Validator Scripts] in
--       Language.Plutus.Coordination.Contracts
swapValidator :: Swap -> ValidatorScript
swapValidator _ = ValidatorScript result where
    result = $$(Ledger.compileScript [|| (\(redeemer :: SwapOracle) SwapOwners{..} (p :: PendingTx) Swap{..} ->
        let
            infixr 3 &&
            (&&) :: Bool -> Bool -> Bool
            (&&) = $$(PlutusTx.and)

            mn :: Int -> Int -> Int
            mn = $$(PlutusTx.min)

            mx :: Int -> Int -> Int
            mx = $$(PlutusTx.max)

            timesR :: Ratio Int -> Ratio Int -> Ratio Int
            timesR (x :% y) (x' :% y') = (x*x') :% (y*y')

            plusR :: Ratio Int -> Ratio Int -> Ratio Int
            plusR (x :% y) (x' :% y') = (x*y' + x'*y) :% (y*y')

            minusR :: Ratio Int -> Ratio Int -> Ratio Int
            minusR (x :% y) (x' :% y') = (x*y' - x'*y) :% (y*y')

            extractVerifyAt :: OracleValue (Ratio Int) -> PubKey -> Ratio Int -> Slot -> Ratio Int
            extractVerifyAt = $$(PlutusTx.error) ()

            round :: Ratio Int -> Int
            round = $$(PlutusTx.error) ()

            -- | Convert an [[Int]] to a [[Ratio Int]]
            fromInt :: Int -> Ratio Int
            fromInt = $$(PlutusTx.error) ()

            signedBy :: PendingTxIn -> PubKey -> Bool
            signedBy = $$(Validation.txInSignedBy)

            infixr 3 ||
            (||) :: Bool -> Bool -> Bool
            (||) = $$(PlutusTx.or)

            isPubKeyOutput :: PendingTxOut -> PubKey -> Bool
            isPubKeyOutput o k = $$(PlutusTx.maybe) False ($$(Validation.eqPubKey) k) ($$(Validation.pubKeyOutput) o)

            -- Verify the authenticity of the oracle value and compute
            -- the payments.
            rt = extractVerifyAt redeemer swapOracle swapFloatingRate swapObservationTime

            rtDiff :: Ratio Int
            rtDiff = rt `minusR` swapFixedRate

            amt = let Value v = swapNotionalAmt in v
            margin = let Value v = swapMargin in v

            amt' :: Ratio Int
            amt' = fromInt amt

            delta :: Ratio Int
            delta = amt' `timesR` rtDiff

            fixedPayment :: Int
            fixedPayment = round (amt' `plusR` delta)

            floatPayment :: Int
            floatPayment = round (amt' `plusR` delta)

            -- Compute the payouts (initial margin +/- the sum of the two
            -- payments), ensuring that it is at least 0 and does not exceed
            -- the total amount of money at stake (2 * margin)
            clamp :: Int -> Int
            clamp x = mn 0 (mx (2 * margin) x)
            fixedRemainder = clamp (margin - fixedPayment + floatPayment)
            floatRemainder = clamp (margin - floatPayment + fixedPayment)

            -- The transaction must have one input from each of the
            -- participants.
            -- NOTE: Partial match is OK because if it fails then the PLC script
            --       terminates with `error` and the validation fails (which is
            --       what we want when the number of inputs and outputs is /= 2)
            PendingTx [t1, t2] [o1, o2] _ _ _ _ = p

            -- Each participant must deposit the margin. But we don't know
            -- which of the two participant's deposit we are currently
            -- evaluating (this script runs on both). So we use the two
            -- predicates iP1 and iP2 to cover both cases

            -- True if the transaction input is the margin payment of the
            -- fixed leg
            iP1 :: PendingTxIn -> Bool
            iP1 t@(PendingTxIn _ _ (Value v)) = signedBy t swapOwnersFixedLeg && v == margin

            -- True if the transaction input is the margin payment of the
            -- floating leg
            iP2 :: PendingTxIn -> Bool
            iP2 t@(PendingTxIn _ _ (Value v)) = signedBy t swapOwnersFloating && v == margin

            inConditions = (iP1 t1  && iP2 t2) || (iP1 t2 && iP2 t1)

            -- The transaction must have two outputs, one for each of the
            -- participants, which equal the margin adjusted by the difference
            -- between fixed and floating payment

            -- True if the output is the payment of the fixed leg.
            ol1 :: PendingTxOut -> Bool
            ol1 o@(PendingTxOut (Value v) _ _) = isPubKeyOutput o swapOwnersFixedLeg && v <= fixedRemainder

            -- True if the output is the payment of the floating leg.
            ol2 :: PendingTxOut -> Bool
            ol2 o@(PendingTxOut (Value v) _ _) = isPubKeyOutput o swapOwnersFloating && v <= floatRemainder

            -- NOTE: I didn't include a check that the slot is greater
            -- than the observation time. This is because the slot is
            -- already part of the oracle value and we trust the oracle.

            outConditions = (ol1 o1 && ol2 o2) || (ol1 o2 && ol2 o1)


        in
        if inConditions && outConditions then () else $$(PlutusTx.error) ()
        ) ||])

{- Note [Swap Transactions]

The swap involves three transactions at two different times.

1. At t=0. Each participant deposits the margin. The outputs are locked with
   the same validator script, `swapValidator`
2. At t=n. The value of the floating rate, and consequently the values of the
   two payments are determined. Each participant gets their margin plus or
   minus the actual payment.

There is a risk of losing out if the interest rate moves outside the range of
fixedRate +/- (margin / notional amount). In a real financial contract this
would be dealt with by agreeing a "Variation Margin". This means that the
margin is adjusted at predefined dates before the actual payment is due. If one
of the parties fails to make the variation margin payment, the contract ends
prematurely and the other party gets to keep both margins.

Plutus should be able to handle variation margins in a series of validation
scripts. But it seems to me that they could get quite messy so I don't want to
write them by hand :) We can probably use TH to generate them at compile time.

-}
