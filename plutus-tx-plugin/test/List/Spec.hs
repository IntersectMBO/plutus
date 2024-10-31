module List.Spec where

import PlutusTx.Data.List qualified as Data.List
import PlutusTx.Prelude qualified as PlutusTx

newtype ListS a = ListS [a]
  deriving stock (Show, Eq)

semanticsToList :: ListS a -> PlutusTx.[a]
semanticsToList (ListS l) = l

listToSemantics :: PlutusTx.[a] -> ListS a
listToSemantics = ListS

semanticsToDataList :: (ToData a) => ListS a -> Data.List.List a
semanticsToDataList = ListS . BI.unsafeDataAsList . B.mkList . fmap toBuiltinData

dataListToSemantics :: (UnsafeFromData a) => Data.List.List a -> ListS a
dataListToSemantics = ListS . go
  where
    go = B.caseList' [] (\h t -> unsafeFromBuiltinData h : go t)

