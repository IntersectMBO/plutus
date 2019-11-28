{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Language.Marlowe.Util where
import           Data.List                  (foldl')
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as Map
import           Data.String

import           Language.Marlowe.Pretty
import           Language.Marlowe.Semantics
import qualified Language.PlutusTx.Prelude  as P
import           Ledger                     (PubKey (..))
import           Ledger.Ada                 (adaSymbol, adaToken)
import qualified Ledger.Value               as Val

instance IsString PubKey where
    fromString = pubKeyFromString

instance IsString AccountId where
    fromString s = AccountId 0 (fromString s)

instance IsString ValueId where
    fromString = ValueId . fromString

ada :: Token
ada = Token adaSymbol adaToken

alicePubKey :: PubKey
alicePubKey = PubKey "Alice"

aliceAcc :: AccountId
aliceAcc = AccountId 0 alicePubKey

bobPubKey :: PubKey
bobPubKey = PubKey "Bob"

bobAcc :: AccountId
bobAcc = AccountId 0 bobPubKey

carolPubKey :: PubKey
carolPubKey = PubKey "Carol"

carolAcc :: AccountId
carolAcc = AccountId 0 carolPubKey

charliePubKey :: PubKey
charliePubKey = PubKey "Charlie"

charlieAcc :: AccountId
charlieAcc = AccountId 0 charliePubKey

evePubKey :: PubKey
evePubKey = PubKey "Eve"

eveAcc :: AccountId
eveAcc = AccountId 0 evePubKey


type AccountsDiff = Map Party Money


emptyAccountsDiff :: AccountsDiff
emptyAccountsDiff = Map.empty


isEmptyAccountsDiff :: AccountsDiff -> Bool
isEmptyAccountsDiff = all Val.isZero


-- Adds a value to the map of outcomes
addAccountsDiff :: Party -> Money -> AccountsDiff -> AccountsDiff
addAccountsDiff party diffValue trOut = let
    newValue = case Map.lookup party trOut of
        Just value -> value P.+ diffValue
        Nothing    -> diffValue
    in Map.insert party newValue trOut


-- | Extract total outcomes from transaction inputs and outputs
getAccountsDiff :: [Payment] -> [Input] -> AccountsDiff
getAccountsDiff payments inputs =
    foldl' (\acc (p, m) -> addAccountsDiff p m acc) emptyAccountsDiff (incomes ++ outcomes)
  where
    incomes  = [ (p,  Val.singleton cur tok m) | IDeposit _ p (Token cur tok) m <- inputs ]
    outcomes = [ (p, P.negate m) | Payment p m  <- payments ]

