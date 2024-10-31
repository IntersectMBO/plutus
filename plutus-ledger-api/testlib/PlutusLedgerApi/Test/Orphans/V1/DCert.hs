{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE LambdaCase #-}

module PlutusLedgerApi.Test.Orphans.V1.DCert () where

import PlutusLedgerApi.Test.Common.QuickCheck.Utils (fromAsWord64)
import PlutusLedgerApi.Test.Orphans.V1.Credential ()
import PlutusLedgerApi.V1.Credential (StakingCredential)
import PlutusLedgerApi.V1.Crypto (PubKeyHash)
-- unqualified improt because formatter + line limit makes it impossible
import PlutusLedgerApi.V1.DCert (DCert (..))
import Test.QuickCheck (Arbitrary (arbitrary, shrink), CoArbitrary (coarbitrary),
                        Function (function), NonNegative (NonNegative), functionMap, getNonNegative,
                        oneof, variant)

instance Arbitrary DCert where
  {-# INLINEABLE arbitrary #-}
  arbitrary =
    oneof
      [ DCertDelegRegKey <$> arbitrary
      , DCertDelegDeRegKey <$> arbitrary
      , DCertDelegDelegate <$> arbitrary <*> arbitrary
      , DCertPoolRegister <$> arbitrary <*> arbitrary
      , DCertPoolRetire <$> arbitrary <*> (fromAsWord64 <$> arbitrary)
      , pure DCertGenesis
      , pure DCertMir
      ]

  {-# INLINEABLE shrink #-}
  shrink = \case
    DCertDelegRegKey sc -> DCertDelegRegKey <$> shrink sc
    DCertDelegDeRegKey sc -> DCertDelegDeRegKey <$> shrink sc
    -- PubKeyHash can't shrink, so we just pass it through, as otherwise, the
    -- semantics of shrinking would mean the whole think can't shrink.
    DCertDelegDelegate sc pkh -> DCertDelegDelegate <$> shrink sc <*> pure pkh
    -- PubKeyHash can't shrink, so neither can this.
    DCertPoolRegister _ _ -> []
    -- PubKeyHash can't shrink, so we just pass it through, as otherwise, the
    -- semantics of shrinking would mean the whole think can't shrink.
    DCertPoolRetire pkh e ->
      DCertPoolRetire pkh . getNonNegative <$> shrink (NonNegative e)
    -- None of the other constructors have any data, so we don't shrink them.
    _ -> []

instance CoArbitrary DCert where
  {-# INLINEABLE coarbitrary #-}
  coarbitrary = \case
    DCertDelegRegKey sc -> variant (0 :: Int) . coarbitrary sc
    DCertDelegDeRegKey sc -> variant (1 :: Int) . coarbitrary sc
    DCertDelegDelegate sc pkh -> variant (2 :: Int) . coarbitrary sc . coarbitrary pkh
    DCertPoolRegister pkh pkh' -> variant (3 :: Int) . coarbitrary pkh . coarbitrary pkh'
    DCertPoolRetire pkh e -> variant (4 :: Int) . coarbitrary pkh . coarbitrary e
    DCertGenesis -> variant (5 :: Int)
    DCertMir -> variant (6 :: Int)

instance Function DCert where
  {-# INLINEABLE function #-}
  function = functionMap into outOf
    where
      into ::
        DCert ->
        Maybe
          ( Maybe
              ( Either
                  StakingCredential
                  ( Either
                      StakingCredential
                      ( Either
                          (StakingCredential, PubKeyHash)
                          ( Either (PubKeyHash, PubKeyHash) (PubKeyHash, Integer)
                          )
                      )
                  )
              )
          )
      into = \case
        DCertGenesis -> Nothing
        DCertMir -> Just Nothing
        DCertDelegRegKey sc -> Just (Just (Left sc))
        DCertDelegDeRegKey sc -> Just (Just (Right (Left sc)))
        DCertDelegDelegate sc pkh -> Just (Just (Right (Right (Left (sc, pkh)))))
        DCertPoolRegister pkh pkh' -> Just (Just (Right (Right (Right (Left (pkh, pkh'))))))
        DCertPoolRetire pkh e -> Just (Just (Right (Right (Right (Right (pkh, e))))))

      outOf ::
        Maybe
          ( Maybe
              ( Either
                  StakingCredential
                  ( Either
                      StakingCredential
                      ( Either
                          (StakingCredential, PubKeyHash)
                          ( Either (PubKeyHash, PubKeyHash) (PubKeyHash, Integer)
                          )
                      )
                  )
              )
          ) ->
        DCert
      outOf = \case
        Nothing -> DCertGenesis
        Just Nothing -> DCertMir
        Just (Just (Left sc)) -> DCertDelegRegKey sc
        Just (Just (Right (Left sc))) -> DCertDelegDeRegKey sc
        Just (Just (Right (Right (Left (sc, pkh))))) -> DCertDelegDelegate sc pkh
        Just (Just (Right (Right (Right (Left (pkh, pkh')))))) -> DCertPoolRegister pkh pkh'
        Just (Just (Right (Right (Right (Right (pkh, e)))))) -> DCertPoolRetire pkh e
