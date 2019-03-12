module Language.Marlowe.Actus where
import           Language.Marlowe
import           Wallet.API       (PubKey (..))


{-|
    A zero-coupon bond is a debt security that doesn't pay interest (a coupon)
    but is traded at a deep discount, rendering profit at maturity
    when the bond is redeemed for its full face value.
-}
zeroCouponBond :: PubKey -> PubKey -> Int -> Int -> Timeout -> Timeout -> Contract
zeroCouponBond issuer investor notional discount startDate maturityDate =
    -- prepare money for zero-coupon bond, before it could be used
    CommitCash (IdentCC 1) investor (Value (notional - discount)) startDate maturityDate
        (CommitCash (IdentCC 2) issuer (Value notional) startDate (maturityDate+1000)
            (When FalseObs startDate Null
                (Pay (IdentPay 1) investor issuer (Committed (IdentCC 1)) maturityDate
                    (When FalseObs maturityDate Null
                        (Pay (IdentPay 2) issuer investor (Committed (IdentCC 2)) (maturityDate+1000) Null)
                    )
                )
            )
            Null
        )
        Null
