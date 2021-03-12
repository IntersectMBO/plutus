module Marlowe.HasParties where

import Prelude
import Data.Array (foldMap)
import Data.Set (Set)
import Data.Set as Set
import Marlowe.Extended as Extended
import Marlowe.Semantics as Semantic

class HasParties a where
  getParties :: a -> Set Semantic.Party

instance arrayHasParties :: HasParties a => HasParties (Array a) where
  getParties = foldMap getParties

instance semanticPartyHasParties :: HasParties Semantic.Party where
  getParties party = Set.singleton party

instance semanticChoiceIdHasParties :: HasParties Semantic.ChoiceId where
  getParties (Semantic.ChoiceId _ party) = getParties party

instance semanticValueHasParties :: HasParties Semantic.Value where
  getParties (Semantic.AvailableMoney accId _) = getParties accId
  getParties (Semantic.Constant _) = Set.empty
  getParties (Semantic.NegValue val) = getParties val
  getParties (Semantic.AddValue lhs rhs) = getParties lhs <> getParties rhs
  getParties (Semantic.SubValue lhs rhs) = getParties lhs <> getParties rhs
  getParties (Semantic.MulValue lhs rhs) = getParties lhs <> getParties rhs
  getParties (Semantic.Scale _ val) = getParties val
  getParties (Semantic.ChoiceValue choId) = getParties choId
  getParties Semantic.SlotIntervalStart = Set.empty
  getParties Semantic.SlotIntervalEnd = Set.empty
  getParties (Semantic.UseValue _) = Set.empty
  getParties (Semantic.Cond obs lhs rhs) = getParties obs <> getParties lhs <> getParties rhs

instance extendedValueHasParties :: HasParties Extended.Value where
  getParties (Extended.AvailableMoney accId _) = getParties accId
  getParties (Extended.Constant _) = Set.empty
  getParties (Extended.ConstantParam _) = Set.empty
  getParties (Extended.NegValue val) = getParties val
  getParties (Extended.AddValue lhs rhs) = getParties lhs <> getParties rhs
  getParties (Extended.SubValue lhs rhs) = getParties lhs <> getParties rhs
  getParties (Extended.MulValue lhs rhs) = getParties lhs <> getParties rhs
  getParties (Extended.Scale _ val) = getParties val
  getParties (Extended.ChoiceValue choId) = getParties choId
  getParties Extended.SlotIntervalStart = Set.empty
  getParties Extended.SlotIntervalEnd = Set.empty
  getParties (Extended.UseValue _) = Set.empty
  getParties (Extended.Cond obs lhs rhs) = getParties obs <> getParties lhs <> getParties rhs

instance semanticObservationHasParties :: HasParties Semantic.Observation where
  getParties (Semantic.AndObs lhs rhs) = getParties lhs <> getParties rhs
  getParties (Semantic.OrObs lhs rhs) = getParties lhs <> getParties rhs
  getParties (Semantic.NotObs v) = getParties v
  getParties (Semantic.ChoseSomething a) = getParties a
  getParties (Semantic.ValueGE lhs rhs) = getParties lhs <> getParties rhs
  getParties (Semantic.ValueGT lhs rhs) = getParties lhs <> getParties rhs
  getParties (Semantic.ValueLT lhs rhs) = getParties lhs <> getParties rhs
  getParties (Semantic.ValueLE lhs rhs) = getParties lhs <> getParties rhs
  getParties (Semantic.ValueEQ lhs rhs) = getParties lhs <> getParties rhs
  getParties Semantic.TrueObs = Set.empty
  getParties Semantic.FalseObs = Set.empty

instance extendedObservationHasParties :: HasParties Extended.Observation where
  getParties (Extended.AndObs lhs rhs) = getParties lhs <> getParties rhs
  getParties (Extended.OrObs lhs rhs) = getParties lhs <> getParties rhs
  getParties (Extended.NotObs v) = getParties v
  getParties (Extended.ChoseSomething a) = getParties a
  getParties (Extended.ValueGE lhs rhs) = getParties lhs <> getParties rhs
  getParties (Extended.ValueGT lhs rhs) = getParties lhs <> getParties rhs
  getParties (Extended.ValueLT lhs rhs) = getParties lhs <> getParties rhs
  getParties (Extended.ValueLE lhs rhs) = getParties lhs <> getParties rhs
  getParties (Extended.ValueEQ lhs rhs) = getParties lhs <> getParties rhs
  getParties Extended.TrueObs = Set.empty
  getParties Extended.FalseObs = Set.empty

instance semanticActionHasParties :: HasParties Semantic.Action where
  getParties (Semantic.Deposit accId party _ value) = getParties accId <> getParties party <> getParties value
  getParties (Semantic.Choice choId _) = getParties choId
  getParties (Semantic.Notify obs) = getParties obs

instance extendedActionHasParties :: HasParties Extended.Action where
  getParties (Extended.Deposit accId party _ value) = getParties accId <> getParties party <> getParties value
  getParties (Extended.Choice choId _) = getParties choId
  getParties (Extended.Notify obs) = getParties obs

instance semanticPayeeHasParties :: HasParties Semantic.Payee where
  getParties (Semantic.Account accountId) = getParties accountId
  getParties (Semantic.Party party) = getParties party

instance extendedPayeeHasParties :: HasParties Extended.Payee where
  getParties (Extended.Account accountId) = getParties accountId
  getParties (Extended.Party party) = getParties party

instance semanticCaseHasParties :: HasParties Semantic.Case where
  getParties (Semantic.Case action contract) = getParties action <> getParties contract

instance extendedCaseHasParties :: HasParties Extended.Case where
  getParties (Extended.Case action contract) = getParties action <> getParties contract

instance semanticContractHasParties :: HasParties Semantic.Contract where
  getParties Semantic.Close = Set.empty
  getParties (Semantic.Pay accId payee _ val cont) = getParties accId <> getParties payee <> getParties val <> getParties cont
  getParties (Semantic.If obs cont1 cont2) = getParties obs <> getParties cont1 <> getParties cont2
  getParties (Semantic.When cases _ cont) = getParties cases <> getParties cont
  getParties (Semantic.Let _ val cont) = getParties val <> getParties cont
  getParties (Semantic.Assert obs cont) = getParties obs <> getParties cont

instance extendedContractHasParties :: HasParties Extended.Contract where
  getParties Extended.Close = Set.empty
  getParties (Extended.Pay accId payee _ val cont) = getParties accId <> getParties payee <> getParties val <> getParties cont
  getParties (Extended.If obs cont1 cont2) = getParties obs <> getParties cont1 <> getParties cont2
  getParties (Extended.When cases _ cont) = getParties cases <> getParties cont
  getParties (Extended.Let _ val cont) = getParties val <> getParties cont
  getParties (Extended.Assert obs cont) = getParties obs <> getParties cont
