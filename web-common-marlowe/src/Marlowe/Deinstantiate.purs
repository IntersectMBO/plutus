module Marlowe.Deinstantiate where

import Prelude
import Data.Array (filter, zipWith)
import Data.BigInteger (BigInteger)
import Data.Foldable (all)
import Data.Generic.Rep (class Generic, Argument(..), Constructor(..), NoArguments, Product(..), Sum(..), from)
import Data.Maybe (Maybe(..))
import Data.Symbol (class IsSymbol)
import Marlowe.Extended as EM
import Marlowe.Extended.Template (ContractTemplate)
import Marlowe.Market (contractTemplates)
import Marlowe.Semantics as S

class IsInstanceOf a b where
  isInstance :: a -> b -> Boolean

class GenericIsInstanceOf a b where
  genericIsInstanceOf' :: a -> b -> Boolean

instance genericIsInstanceOfSum :: (GenericIsInstanceOf a c, GenericIsInstanceOf b c) => GenericIsInstanceOf (Sum a b) c where
  genericIsInstanceOf' (Inl a) c = genericIsInstanceOf' a c
  genericIsInstanceOf' (Inr b) c = genericIsInstanceOf' b c
else instance genericIsInstanceOfSum2 :: (GenericIsInstanceOf a b, GenericIsInstanceOf a c) => GenericIsInstanceOf a (Sum b c) where
  genericIsInstanceOf' a (Inl b) = genericIsInstanceOf' a b
  genericIsInstanceOf' a (Inr c) = genericIsInstanceOf' a c

instance genericIsInstanceOfSlotParam :: (GenericIsInstanceOf a b) => GenericIsInstanceOf (Constructor "Constant" a) (Constructor "ConstantParam" b) where
  genericIsInstanceOf' (Constructor a) (Constructor b) = true
else instance genericIsInstanceOfEqConstructor :: (GenericIsInstanceOf a b, IsSymbol nameA) => GenericIsInstanceOf (Constructor nameA a) (Constructor nameA b) where
  genericIsInstanceOf' (Constructor a) (Constructor b) = genericIsInstanceOf' a b
else instance genericIsInstanceOfConstructor :: (IsSymbol nameA, IsSymbol nameB) => GenericIsInstanceOf (Constructor nameA a) (Constructor nameB b) where
  genericIsInstanceOf' (Constructor a) (Constructor b) = false

instance genericIsInstanceOfNoArguments :: GenericIsInstanceOf NoArguments NoArguments where
  genericIsInstanceOf' _ _ = true
else instance genericIsInstanceOfProduct :: (GenericIsInstanceOf a1 b1, GenericIsInstanceOf a2 b2) => GenericIsInstanceOf (Product a1 a2) (Product b1 b2) where
  genericIsInstanceOf' (Product a1 a2) (Product b1 b2) = genericIsInstanceOf' a1 b1 && genericIsInstanceOf' a2 b2

instance genericIsInstanceOfSame :: Eq a => GenericIsInstanceOf (Argument a) (Argument a) where
  genericIsInstanceOf' (Argument a) (Argument b) = a == b
else instance genericIsInstanceOfArguments :: IsInstanceOf a b => GenericIsInstanceOf (Argument a) (Argument b) where
  genericIsInstanceOf' (Argument a) (Argument b) = isInstance a b

genericIsInstanceOf :: forall a b repA repB. Generic a repA => Generic b repB => GenericIsInstanceOf repA repB => a -> b -> Boolean
genericIsInstanceOf a b = genericIsInstanceOf' (from a) (from b)

instance isInstanceOfPayee :: IsInstanceOf S.Payee EM.Payee where
  isInstance a b = genericIsInstanceOf a b

instance isInstanceOfBigIntegerString :: IsInstanceOf BigInteger String where
  isInstance a b = false

instance isInstanceOfValue :: IsInstanceOf S.Value EM.Value where
  isInstance a b = genericIsInstanceOf a b

instance isInstanceOfObservation :: IsInstanceOf S.Observation EM.Observation where
  isInstance a b = genericIsInstanceOf a b

instance isInstanceOfAction :: IsInstanceOf S.Action EM.Action where
  isInstance a b = genericIsInstanceOf a b

instance isInstanceOfCase :: IsInstanceOf S.Case EM.Case where
  isInstance a b = genericIsInstanceOf a b

instance isInstanceOfArrayOfCase :: IsInstanceOf (Array S.Case) (Array EM.Case) where
  isInstance a b = all identity (zipWith isInstance a b)

instance isInstanceOfSlotTimeout :: IsInstanceOf S.Slot EM.Timeout where
  isInstance _ (EM.SlotParam _) = true
  isInstance (S.Slot x) (EM.Slot y) = x == y

instance isInstanceOfContract :: IsInstanceOf S.Contract EM.Contract where
  isInstance a b = genericIsInstanceOf a b

findTemplate :: S.Contract -> Maybe ContractTemplate
findTemplate contract = case filter (\candidate -> isInstance contract candidate.extendedContract) contractTemplates of
  [ template ] -> Just template
  _ -> Nothing
