module Marlowe.Parser where

import Prelude

import Control.Alternative ((<|>))
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.List (List)
import Data.Maybe (Maybe(..))
import Data.Newtype (wrap)
import Marlowe.Types (BlockNumber, Choice, Contract(..), IdAction, IdChoice, IdCommit, IdOracle, LetLabel, Observation(..), Person, Timeout, Value(..))
import Text.Parsing.Simple (Parser, char, fail, fix, integral, parens, some, space, string, whitespace)

-- All arguments are space separated so we add **> to reduce boilerplate

spaces :: Parser String (List Char)
spaces = some whitespace

appRSpaces :: forall a b. Parser String a -> Parser String b -> Parser String b
appRSpaces p q = p *> spaces *> q

infixl 4 appRSpaces as **>

appSpaces :: forall a b. Parser String (a -> b) -> Parser String a -> Parser String b
appSpaces p q = p <*> (spaces *> q)

infixl 4 appSpaces as <**>

------------------------------------------------------------------------

bigInteger :: Parser String BigInteger
bigInteger = do
    i <- integral
    case BigInteger.fromString i of
      (Just v) -> pure v
      Nothing -> fail "not a valid BigInt"

idChoice :: Parser String IdChoice
idChoice = parens do
  first <- bigInteger
  void $ char ','
  void space
  second <- bigInteger
  pure $ wrap { choice: first, person: second }

choice :: Parser String Choice
choice = bigInteger

blockNumber :: Parser String BlockNumber
blockNumber = bigInteger

timeout :: Parser String Timeout
timeout = blockNumber

idOracle :: Parser String IdOracle
idOracle = bigInteger

idCommit :: Parser String IdCommit
idCommit = bigInteger

idAction :: Parser String IdAction
idAction = bigInteger

person :: Parser String Person
person = bigInteger

letLabel :: Parser String LetLabel
letLabel = bigInteger

atomValue :: Parser String Value
atomValue = pure CurrentBlock <* string "CurrentBlock"

recValue :: Parser String Value
recValue =
    Committed <$> (string "Committed" **> idCommit)
    <|> Constant <$> (string "Constant" **> bigInteger)
    <|> NegValue <$> (string "NegValue" **> value')
    <|> AddValue <$> (string "AddValue" **> value') <**> value'
    <|> SubValue <$> (string "SubValue" **> value') <**> value'
    <|> MulValue <$> (string "MulValue" **> value') <**> value'
    <|> DivValue <$> (string "DivValue" **> value') <**> value' <**> value'
    <|> ModValue <$> (string "ModValue" **> value') <**> value' <**> value'
    <|> ValueFromChoice <$> (string "ValueFromChoice" **> idChoice) <**> value'
    <|> ValueFromOracle <$> (string "ValueFromOracle" **> idOracle) <**> value'
  where
    value' :: Parser String Value
    value' = atomValue <|> fix (\p -> parens recValue)

value :: Parser String Value
value = atomValue <|> recValue

atomObservation :: Parser String Observation
atomObservation
  =   pure TrueObs <* string "TrueObs"
  <|> pure FalseObs <* string "FalseObs"

recObservation :: Parser String Observation
recObservation 
    =   BelowTimeout <$> (string "BelowTimeout" **> timeout)
    <|> AndObs <$> (string "AndObs" **> observation') <**> observation'
    <|> OrObs <$> (string "OrObs" **> observation') <**> observation'
    <|> NotObs <$> (string "NotObs" **> observation')
    <|> ChoseThis <$> (string "ChoseThis" **> idChoice) <**> choice
    <|> ChoseSomething <$> (string "ChoseSomething" **> idChoice)
    <|> ValueGE <$> (string "ValueGE" **> value') <**> value'
    <|> ValueGT <$> (string "ValueGT" **> value') <**> value'
    <|> ValueLT <$> (string "ValueLT" **> value') <**> value'
    <|> ValueLE <$> (string "ValueLE" **> value') <**> value'
    <|> ValueEQ <$> (string "ValueEQ" **> value') <**> value'
  where
    observation' = atomObservation <|> fix \p -> parens recObservation
    value' = atomValue <|> fix (\p -> parens value)

observation :: Parser String Observation
observation = atomObservation <|> recObservation

atomContract :: Parser String Contract
atomContract = pure Null <* string "Null"

recContract :: Parser String Contract
recContract
    =   Commit <$> (string "Commit" **> idAction) 
               <**> idCommit 
               <**> person 
               <**> value' 
               <**> timeout 
               <**> timeout
               <**> contract'
               <**> contract'
    <|> Pay <$> (string "Pay" **> idAction) 
            <**> idCommit
            <**> person
            <**> value'
            <**> timeout 
            <**> contract' 
            <**> contract'
    <|> Both <$> (string "Both" **> contract') <**> contract'
    <|> Choice <$> (string "Choice" **> observation') <**> contract' <**> contract'
    <|> When <$> (string "When" **> observation') <**> timeout <**> contract' <**> contract'
    <|> While <$> (string "While" **> observation') <**> timeout <**> contract' <**> contract'
    <|> Scale <$> (string "Scale" **> value') <**> value' <**> value' <**> contract'
    <|> Let <$> (string "Let" **> letLabel) <**> contract' <**> contract'
    <|> Use <$> (string "Use" **> letLabel)
    <|> fail "not a valid Contract"
  where
    contract' = atomContract <|> fix \p -> parens recContract
    observation' = atomObservation <|> fix \p -> parens observation
    value' = atomValue <|> fix (\p -> parens value)

contract :: Parser String Contract
contract = atomContract <|> recContract