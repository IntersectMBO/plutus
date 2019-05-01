module Marlowe.Parser where

import Prelude

import Control.Alternative ((<|>))
import Control.Lazy (fix)
import Data.BigInt (BigInt)
import Data.BigInt as BigInt
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.List (List, many, some)
import Data.Maybe (Maybe(..))
import Data.Newtype (wrap)
import Marlowe.Types (BlockNumber(BlockNumber), Choice, Contract(..), IdAction(IdAction), IdChoice, IdCommit(IdCommit), IdOracle(IdOracle), LetLabel, Observation(..), Person(Person), Timeout(Timeout), Value(..))
import Text.Parsing.Parser (Parser, fail)
import Text.Parsing.Parser.Basic (integral, parens)
import Text.Parsing.Parser.String (char, string)
import Text.Parsing.Parser.Token (space)

-- All arguments are space separated so we add **> to reduce boilerplate

maybeSpaces :: Parser String (List Char)
maybeSpaces = many space

spaces :: Parser String (List Char)
spaces = some space

appRSpaces :: forall a b. Parser String a -> Parser String b -> Parser String b
appRSpaces p q = p *> spaces *> q

infixl 4 appRSpaces as **>

appSpaces :: forall a b. Parser String (a -> b) -> Parser String a -> Parser String b
appSpaces p q = p <*> (spaces *> q)

infixl 4 appSpaces as <**>

----------------------------------------------------------------------

bigInteger :: Parser String BigInteger
bigInteger = do
    i <- integral
    case BigInteger.fromString i of
      (Just v) -> pure v
      Nothing -> fail "not a valid BigInt"

bigInt :: Parser String BigInt
bigInt = do
    i <- integral
    case BigInt.fromString i of
      (Just v) -> pure v
      Nothing -> fail "not a valid BigInt"

person :: Parser String Person
person = Person <$> bigInt

idChoice :: Parser String IdChoice
idChoice = parens do
  void maybeSpaces 
  first <- bigInteger
  void maybeSpaces 
  void $ char ','
  void maybeSpaces 
  second <- person
  void maybeSpaces 
  pure $ wrap { choice: first, person: second }

choice :: Parser String Choice
choice = bigInteger

blockNumber :: Parser String BlockNumber
blockNumber = BlockNumber <$> bigInt

timeout :: Parser String Timeout
timeout = Timeout <$> blockNumber

idOracle :: Parser String IdOracle
idOracle = IdOracle <$> bigInteger

idCommit :: Parser String IdCommit
idCommit = IdCommit <$> bigInteger

idAction :: Parser String IdAction
idAction = IdAction <$> bigInteger

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
-- 
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
contract = do void maybeSpaces
              c <- (atomContract <|> recContract)
              void maybeSpaces
              pure c