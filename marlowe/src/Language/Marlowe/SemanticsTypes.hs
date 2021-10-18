{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TemplateHaskell            #-}

-- Big hammer, but helps
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-warn-orphans       #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module Language.Marlowe.SemanticsTypes where

import           Control.Applicative         ((<*>), (<|>))
import           Control.Newtype.Generics    (Newtype)
import qualified Data.Aeson                  as JSON
import qualified Data.Aeson.Extras           as JSON
import           Data.Aeson.Types            hiding (Error, Value)
import qualified Data.Foldable               as F
import           Data.Scientific             (Scientific)
import           Data.String                 (IsString (..))
import           Data.Text                   (pack)
import           Data.Text.Encoding          as Text (decodeUtf8, encodeUtf8)
import           Deriving.Aeson
import           Language.Marlowe.ParserUtil (getInteger, withInteger)
import           Language.Marlowe.Pretty     (Pretty (..))
import           Ledger                      (PubKeyHash (..), Slot (..))
import           Ledger.Value                (CurrencySymbol (..), TokenName (..))
import qualified Ledger.Value                as Val
import           PlutusTx                    (makeIsDataIndexed)
import           PlutusTx.AssocMap           (Map)
import qualified PlutusTx.AssocMap           as Map
import           PlutusTx.Lift               (makeLift)
import           PlutusTx.Prelude            hiding (encodeUtf8, mapM, (<$>), (<*>), (<>))
import           PlutusTx.Ratio              (denominator, numerator)
import           Prelude                     (mapM, (<$>))
import qualified Prelude                     as Haskell


{- Functions that used in Plutus Core must be inlineable,
   so their code is available for PlutusTx compiler -}
{-# INLINABLE inBounds #-}
{-# INLINABLE emptyState #-}

{-| = Type definitions for Marlowe's seamntics
-}

data Party = PK PubKeyHash | Role TokenName
  deriving stock (Generic,Haskell.Eq,Haskell.Ord)
  deriving anyclass (Pretty)

instance Haskell.Show Party where
  showsPrec p (PK pk) = Haskell.showParen (p Haskell.>= 11) $ Haskell.showString "PK \""
                                              . Haskell.showsPrec 11 pk
                                              . Haskell.showString "\""
  showsPrec _ (Role role) = Haskell.showsPrec 11 $ unTokenName role

type AccountId = Party
type Timeout = Slot
type Money = Val.Value
type ChoiceName = BuiltinByteString
type ChosenNum = Integer
type SlotInterval = (Slot, Slot)
type Accounts = Map (AccountId, Token) Integer

-- * Data Types
{-| Choices – of integers – are identified by ChoiceId
    which combines a name for the choice with the Party who had made the choice.
-}
data ChoiceId = ChoiceId BuiltinByteString Party
  deriving stock (Haskell.Show,Generic,Haskell.Eq,Haskell.Ord)
  deriving anyclass (Pretty)


{-| Token - represents a currency or token, it groups
    a pair of a currency symbol and token name.
-}
data Token = Token CurrencySymbol TokenName
  deriving stock (Generic,Haskell.Eq,Haskell.Ord)
  deriving anyclass (Pretty)

instance Haskell.Show Token where
  showsPrec p (Token cs tn) =
    Haskell.showParen (p Haskell.>= 11) (Haskell.showString $ "Token \"" Haskell.++ Haskell.show cs Haskell.++ "\" " Haskell.++ Haskell.show tn)

{-| Values, as defined using Let ar e identified by name,
    and can be used by 'UseValue' construct.
-}
newtype ValueId = ValueId BuiltinByteString
  deriving (IsString, Haskell.Show) via TokenName
  deriving stock (Haskell.Eq,Haskell.Ord,Generic)
  deriving anyclass (Newtype)

{-| Values include some quantities that change with time,
    including “the slot interval”, “the current balance of an account (in Lovelace)”,
    and any choices that have already been made.

    Values can also be scaled, and combined using addition, subtraction, and negation.
-}
data Value a = AvailableMoney AccountId Token
           | Constant Integer
           | NegValue (Value a)
           | AddValue (Value a) (Value a)
           | SubValue (Value a) (Value a)
           | MulValue (Value a) (Value a)
           | DivValue (Value a) (Value a)
           | Scale Rational (Value a)
           | ChoiceValue ChoiceId
           | SlotIntervalStart
           | SlotIntervalEnd
           | UseValue ValueId
           | Cond a (Value a) (Value a)
  deriving stock (Haskell.Show,Generic,Haskell.Eq,Haskell.Ord)
  deriving anyclass (Pretty)


{-| Observations are Boolean values derived by comparing values,
    and can be combined using the standard Boolean operators.

    It is also possible to observe whether any choice has been made
    (for a particular identified choice).
-}
data Observation = AndObs Observation Observation
                 | OrObs Observation Observation
                 | NotObs Observation
                 | ChoseSomething ChoiceId
                 | ValueGE (Value Observation) (Value Observation)
                 | ValueGT (Value Observation) (Value Observation)
                 | ValueLT (Value Observation) (Value Observation)
                 | ValueLE (Value Observation) (Value Observation)
                 | ValueEQ (Value Observation) (Value Observation)
                 | TrueObs
                 | FalseObs
  deriving stock (Haskell.Show,Generic,Haskell.Eq,Haskell.Ord)
  deriving anyclass (Pretty)


data Bound = Bound Integer Integer
  deriving stock (Haskell.Show,Generic,Haskell.Eq,Haskell.Ord)
  deriving anyclass (Pretty)


{-| Actions happen at particular points during execution.
    Three kinds of action are possible:

    * A @Deposit n p v@ makes a deposit of value @v@ into account @n@ belonging to party @p@.

    * A choice is made for a particular id with a list of bounds on the values that are acceptable.
      For example, @[(0, 0), (3, 5]@ offers the choice of one of 0, 3, 4 and 5.

    * The contract is notified that a particular observation be made.
      Typically this would be done by one of the parties,
      or one of their wallets acting automatically.
-}
data Action = Deposit AccountId Party Token (Value Observation)
            | Choice ChoiceId [Bound]
            | Notify Observation
  deriving stock (Haskell.Show,Generic,Haskell.Eq,Haskell.Ord)
  deriving anyclass (Pretty)


{-| A payment can be made to one of the parties to the contract,
    or to one of the accounts of the contract,
    and this is reflected in the definition.
-}
data Payee = Account AccountId
           | Party Party
  deriving stock (Haskell.Show,Generic,Haskell.Eq,Haskell.Ord)
  deriving anyclass (Pretty)


{-  Plutus doesn't support mutually recursive data types yet.
    datatype Case is mutually recurvive with @Contract@
-}
data Case a = Case Action a
  deriving stock (Haskell.Show,Generic,Haskell.Eq,Haskell.Ord)
  deriving anyclass (Pretty)


{-| Marlowe has six ways of building contracts.
    Five of these – 'Pay', 'Let', 'If', 'When' and 'Assert' –
    build a complex contract from simpler contracts, and the sixth, 'Close',
    is a simple contract.
    At each step of execution, as well as returning a new state and continuation contract,
    it is possible that effects – payments – and warnings can be generated too.
-}
data Contract = Close
              | Pay AccountId Payee Token (Value Observation) Contract
              | If Observation Contract Contract
              | When [Case Contract] Timeout Contract
              | Let ValueId (Value Observation) Contract
              | Assert Observation Contract
  deriving stock (Haskell.Show,Generic,Haskell.Eq,Haskell.Ord)
  deriving anyclass (Pretty)


{-| Marlowe contract internal state. Stored in a /Datum/ of a transaction output.
-}
data State = State { accounts    :: Accounts
                   , choices     :: Map ChoiceId ChosenNum
                   , boundValues :: Map ValueId Integer
                   , minSlot     :: Slot }
  deriving stock (Haskell.Show,Haskell.Eq,Generic)

{-| Execution environment. Contains a slot interval of a transaction.
-}
newtype Environment = Environment { slotInterval :: SlotInterval }
  deriving stock (Haskell.Show,Haskell.Eq,Haskell.Ord)


{-| Input for a Marlowe contract. Correspond to expected 'Action's.
-}
data Input = IDeposit AccountId Party Token Integer
           | IChoice ChoiceId ChosenNum
           | INotify
  deriving stock (Haskell.Show,Haskell.Eq,Generic)
  deriving anyclass (Pretty)

instance FromJSON Input where
  parseJSON (String "input_notify") = return INotify
  parseJSON (Object v) =
        (IDeposit <$> (v .: "into_account")
                  <*> (v .: "input_from_party")
                  <*> (v .: "of_token")
                  <*> (v .: "that_deposits"))
    <|> (IChoice <$> (v .: "for_choice_id")
                 <*> (v .: "input_that_chooses_num"))
  parseJSON _ = Haskell.fail "Contract must be either an object or a the string \"close\""

instance ToJSON Input where
  toJSON (IDeposit accId party tok amount) = object
      [ "input_from_party" .= party
      , "that_deposits" .= amount
      , "of_token" .= tok
      , "into_account" .= accId
      ]
  toJSON (IChoice choiceId chosenNum) = object
      [ "input_that_chooses_num" .= chosenNum
      , "for_choice_id" .= choiceId
      ]
  toJSON INotify = JSON.String $ pack "input_notify"


{-| Slot interval errors.
    'InvalidInterval' means @slotStart > slotEnd@, and
    'IntervalInPastError' means slot interval is in the past, relative to the contract.

    These errors should never occur, but we are always prepared.
-}
data IntervalError = InvalidInterval SlotInterval
                   | IntervalInPastError Slot SlotInterval
  deriving stock (Haskell.Show, Generic, Haskell.Eq)
  deriving anyclass (ToJSON, FromJSON)


-- | Result of 'fixInterval'
data IntervalResult = IntervalTrimmed Environment State
                    | IntervalError IntervalError
  deriving stock (Haskell.Show)


-- | Empty State for a given minimal 'Slot'
emptyState :: Slot -> State
emptyState sn = State
    { accounts = Map.empty
    , choices  = Map.empty
    , boundValues = Map.empty
    , minSlot = sn }


-- | Check if a 'num' is withint a list of inclusive bounds.
inBounds :: ChosenNum -> [Bound] -> Bool
inBounds num = any (\(Bound l u) -> num >= l && num <= u)


instance FromJSON State where
  parseJSON = withObject "State" (\v ->
         State <$> (v .: "accounts")
               <*> (v .: "choices")
               <*> (v .: "boundValues")
               <*> (Slot <$> (withInteger =<< (v .: "minSlot")))
                                 )

instance ToJSON State where
  toJSON State { accounts = a
               , choices = c
               , boundValues = bv
               , minSlot = Slot ms } = object
        [ "accounts" .= a
        , "choices" .= c
        , "boundValues" .= bv
        , "minSlot" .= ms ]

instance FromJSON Party where
  parseJSON = withObject "Party" (\v ->
        (PK . PubKeyHash . toBuiltin <$> (JSON.decodeByteString =<< (v .: "pk_hash")))
    <|> (Role . Val.tokenName . Text.encodeUtf8 <$> (v .: "role_token"))
                                 )
instance ToJSON Party where
    toJSON (PK pkh) = object
        [ "pk_hash" .= (JSON.String $ JSON.encodeByteString $ fromBuiltin $ getPubKeyHash pkh) ]
    toJSON (Role (Val.TokenName name)) = object
        [ "role_token" .= (JSON.String $ Text.decodeUtf8 $ fromBuiltin name) ]


instance FromJSON ChoiceId where
  parseJSON = withObject "ChoiceId" (\v ->
       ChoiceId <$> (toBuiltin . Text.encodeUtf8 <$> (v .: "choice_name"))
                <*> (v .: "choice_owner")
                                    )

instance ToJSON ChoiceId where
  toJSON (ChoiceId name party) = object [ "choice_name" .= (JSON.String $ Text.decodeUtf8 $ fromBuiltin name)
                                        , "choice_owner" .= party
                                        ]


instance FromJSON Token where
  parseJSON = withObject "Token" (\v ->
       Token <$> (Val.currencySymbol <$> (JSON.decodeByteString =<< (v .: "currency_symbol")))
             <*> (Val.tokenName . Text.encodeUtf8 <$> (v .: "token_name"))
                                 )

instance ToJSON Token where
  toJSON (Token currSym tokName) = object
      [ "currency_symbol" .= (JSON.String $ JSON.encodeByteString $ fromBuiltin $ unCurrencySymbol currSym)
      , "token_name" .= (JSON.String $ Text.decodeUtf8 $ fromBuiltin $ unTokenName tokName)
      ]

instance FromJSON ValueId where
    parseJSON = withText "ValueId" $ return . ValueId . toBuiltin . Text.encodeUtf8
instance ToJSON ValueId where
    toJSON (ValueId x) = JSON.String (Text.decodeUtf8 $ fromBuiltin x)


instance FromJSON (Value Observation) where
  parseJSON (Object v) =
        (AvailableMoney <$> (v .: "in_account")
                        <*> (v .: "amount_of_token"))
    <|> (NegValue <$> (v .: "negate"))
    <|> (AddValue <$> (v .: "add")
                  <*> (v .: "and"))
    <|> (SubValue <$> (v .: "value")
                  <*> (v .: "minus"))
    <|> (do maybeDiv <- v .:? "divide_by"
            case maybeDiv :: Maybe Scientific of
              Nothing -> MulValue <$> (v .: "multiply")
                                  <*> (v .: "times")
              Just divi -> Scale <$> ((%) <$> (getInteger =<< (v .: "times")) <*> getInteger divi)
                                 <*> (v .: "multiply"))
    <|> (DivValue <$> (v .: "divide") <*> (v .: "by"))
    <|> (ChoiceValue <$> (v .: "value_of_choice"))
    <|> (UseValue <$> (v .: "use_value"))
    <|> (Cond <$> (v .: "if")
              <*> (v .: "then")
              <*> (v .: "else"))
  parseJSON (String "slot_interval_start") = return SlotIntervalStart
  parseJSON (String "slot_interval_end") = return SlotIntervalEnd
  parseJSON (Number n) = Constant <$> getInteger n
  parseJSON _ = Haskell.fail "Value must be either an object or an integer"
instance ToJSON (Value Observation) where
  toJSON (AvailableMoney accountId token) = object
      [ "amount_of_token" .= token
      , "in_account" .= accountId
      ]
  toJSON (Constant x) = toJSON x
  toJSON (NegValue x) = object
      [ "negate" .= x ]
  toJSON (AddValue lhs rhs) = object
      [ "add" .= lhs
      , "and" .= rhs
      ]
  toJSON (SubValue lhs rhs) = object
      [ "value" .= lhs
      , "minus" .= rhs
      ]
  toJSON (MulValue lhs rhs) = object
      [ "multiply" .= lhs
      , "times" .= rhs
      ]
  toJSON (DivValue lhs rhs) = object
      [ "divide" .= lhs
      , "by" .= rhs
      ]
  toJSON (Scale rat v) = object
      [ "multiply" .= v
      , "times" .= num
      , "divide_by" .= den
      ]
    where num = numerator rat
          den = denominator rat
  toJSON (ChoiceValue choiceId) = object
      [ "value_of_choice" .= choiceId ]
  toJSON SlotIntervalStart = JSON.String $ pack "slot_interval_start"
  toJSON SlotIntervalEnd = JSON.String $ pack "slot_interval_end"
  toJSON (UseValue valueId) = object
      [ "use_value" .= valueId ]
  toJSON (Cond obs tv ev) = object
      [ "if" .= obs
      , "then" .= tv
      , "else" .= ev
      ]


instance FromJSON Observation where
  parseJSON (Bool True) = return TrueObs
  parseJSON (Bool False) = return FalseObs
  parseJSON (Object v) =
        (AndObs <$> (v .: "both")
                <*> (v .: "and"))
    <|> (OrObs <$> (v .: "either")
               <*> (v .: "or"))
    <|> (NotObs <$> (v .: "not"))
    <|> (ChoseSomething <$> (v .: "chose_something_for"))
    <|> (ValueGE <$> (v .: "value")
                 <*> (v .: "ge_than"))
    <|> (ValueGT <$> (v .: "value")
                 <*> (v .: "gt"))
    <|> (ValueLT <$> (v .: "value")
                 <*> (v .: "lt"))
    <|> (ValueLE <$> (v .: "value")
                 <*> (v .: "le_than"))
    <|> (ValueEQ <$> (v .: "value")
                 <*> (v .: "equal_to"))
  parseJSON _ = Haskell.fail "Observation must be either an object or a boolean"

instance ToJSON Observation where
  toJSON (AndObs lhs rhs) = object
      [ "both" .= lhs
      , "and" .= rhs
      ]
  toJSON (OrObs lhs rhs) = object
      [ "either" .= lhs
      , "or" .= rhs
      ]
  toJSON (NotObs v) = object
      [ "not" .= v ]
  toJSON (ChoseSomething choiceId) = object
      [ "chose_something_for" .= choiceId ]
  toJSON (ValueGE lhs rhs) = object
      [ "value" .= lhs
      , "ge_than" .= rhs
      ]
  toJSON (ValueGT lhs rhs) = object
      [ "value" .= lhs
      , "gt" .= rhs
      ]
  toJSON (ValueLT lhs rhs) = object
      [ "value" .= lhs
      , "lt" .= rhs
      ]
  toJSON (ValueLE lhs rhs) = object
      [ "value" .= lhs
      , "le_than" .= rhs
      ]
  toJSON (ValueEQ lhs rhs) = object
      [ "value" .= lhs
      , "equal_to" .= rhs
      ]
  toJSON TrueObs = toJSON True
  toJSON FalseObs = toJSON False


instance FromJSON Bound where
  parseJSON = withObject "Bound" (\v ->
       Bound <$> (getInteger =<< (v .: "from"))
             <*> (getInteger =<< (v .: "to"))
                                 )
instance ToJSON Bound where
  toJSON (Bound from to) = object
      [ "from" .= from
      , "to" .= to
      ]

instance FromJSON Action where
  parseJSON = withObject "Action" (\v ->
       (Deposit <$> (v .: "into_account")
                <*> (v .: "party")
                <*> (v .: "of_token")
                <*> (v .: "deposits"))
   <|> (Choice <$> (v .: "for_choice")
               <*> ((v .: "choose_between") >>=
                    withArray "Bound list" (\bl ->
                      mapM parseJSON (F.toList bl)
                                            )))
   <|> (Notify <$> (v .: "notify_if"))
                                  )
instance ToJSON Action where
  toJSON (Deposit accountId party token val) = object
      [ "into_account" .= accountId
      , "party" .= party
      , "of_token" .= token
      , "deposits" .= val
      ]
  toJSON (Choice choiceId bounds) = object
      [ "for_choice" .= choiceId
      , "choose_between" .= toJSONList (map toJSON bounds)
      ]
  toJSON (Notify obs) = object
      [ "notify_if" .= obs ]


instance FromJSON Payee where
  parseJSON = withObject "Payee" (\v ->
                (Account <$> (v .: "account"))
            <|> (Party <$> (v .: "party")))

instance ToJSON Payee where
  toJSON (Account acc) = object ["account" .= acc]
  toJSON (Party party) = object ["party" .= party]


instance FromJSON a => FromJSON (Case a) where
  parseJSON = withObject "Case" (\v ->
       Case <$> (v .: "case")
            <*> (v .: "then")
                                )
instance ToJSON a => ToJSON (Case a) where
  toJSON (Case act cont) = object
      [ "case" .= act
      , "then" .= cont
      ]


instance FromJSON Contract where
  parseJSON (String "close") = return Close
  parseJSON (Object v) =
        (Pay <$> (v .: "from_account")
             <*> (v .: "to")
             <*> (v .: "token")
             <*> (v .: "pay")
             <*> (v .: "then"))
    <|> (If <$> (v .: "if")
            <*> (v .: "then")
            <*> (v .: "else"))
    <|> (When <$> ((v .: "when") >>=
                   withArray "Case list" (\cl ->
                     mapM parseJSON (F.toList cl)
                                          ))
              <*> (Slot <$> (withInteger =<< (v .: "timeout")))
              <*> (v .: "timeout_continuation"))
    <|> (Let <$> (v .: "let")
             <*> (v .: "be")
             <*> (v .: "then"))
    <|> (Assert <$> (v .: "assert")
                <*> (v .: "then"))
  parseJSON _ = Haskell.fail "Contract must be either an object or a the string \"close\""

instance ToJSON Contract where
  toJSON Close = JSON.String $ pack "close"
  toJSON (Pay accountId payee token value contract) = object
      [ "from_account" .= accountId
      , "to" .= payee
      , "token" .= token
      , "pay" .= value
      , "then" .= contract
      ]
  toJSON (If obs cont1 cont2) = object
      [ "if" .= obs
      , "then" .= cont1
      , "else" .= cont2
      ]
  toJSON (When caseList timeout cont) = object
      [ "when" .= toJSONList (map toJSON caseList)
      , "timeout" .= getSlot timeout
      , "timeout_continuation" .= cont
      ]
  toJSON (Let valId value cont) = object
      [ "let" .= valId
      , "be" .= value
      , "then" .= cont
      ]
  toJSON (Assert obs cont) = object
      [ "assert" .= obs
      , "then" .= cont
      ]


instance Eq Party where
    {-# INLINABLE (==) #-}
    (PK p1) == (PK p2)     = p1 == p2
    (Role r1) == (Role r2) = r1 == r2
    _ == _                 = False


instance Eq ChoiceId where
    {-# INLINABLE (==) #-}
    (ChoiceId n1 p1) == (ChoiceId n2 p2) = n1 == n2 && p1 == p2

instance Eq Token where
    {-# INLINABLE (==) #-}
    (Token n1 p1) == (Token n2 p2) = n1 == n2 && p1 == p2

instance Eq ValueId where
    {-# INLINABLE (==) #-}
    (ValueId n1) == (ValueId n2) = n1 == n2


instance Pretty ValueId where
    prettyFragment (ValueId n) = prettyFragment n

instance Eq Payee where
    {-# INLINABLE (==) #-}
    Account acc1 == Account acc2 = acc1 == acc2
    Party p1 == Party p2         = p1 == p2
    _ == _                       = False


instance Eq a => Eq (Value a) where
    {-# INLINABLE (==) #-}
    AvailableMoney acc1 tok1 == AvailableMoney acc2 tok2 =
        acc1 == acc2 && tok1 == tok2
    Constant i1 == Constant i2 = i1 == i2
    NegValue val1 == NegValue val2 = val1 == val2
    AddValue val1 val2 == AddValue val3 val4 = val1 == val3 && val2 == val4
    SubValue val1 val2 == SubValue val3 val4 = val1 == val3 && val2 == val4
    MulValue val1 val2 == MulValue val3 val4 = val1 == val3 && val2 == val4
    DivValue val1 val2 == DivValue val3 val4 = val1 == val3 && val2 == val4
    Scale s1 val1 == Scale s2 val2 = s1 == s2 && val1 == val2
    ChoiceValue cid1 == ChoiceValue cid2 = cid1 == cid2
    SlotIntervalStart == SlotIntervalStart = True
    SlotIntervalEnd   == SlotIntervalEnd   = True
    UseValue val1 == UseValue val2 = val1 == val2
    Cond obs1 thn1 els1 == Cond obs2 thn2 els2 =  obs1 == obs2 && thn1 == thn2 && els1 == els2
    _ == _ = False

instance Eq Observation where
    {-# INLINABLE (==) #-}
    AndObs o1l o2l == AndObs o1r o2r           = o1l == o1r && o2l == o2r
    OrObs  o1l o2l == OrObs  o1r o2r           = o1l == o1r && o2l == o2r
    NotObs ol == NotObs or                     = ol == or
    ChoseSomething cid1 == ChoseSomething cid2 = cid1 == cid2
    ValueGE v1l v2l == ValueGE v1r v2r         = v1l == v1r && v2l == v2r
    ValueGT v1l v2l == ValueGT v1r v2r         = v1l == v1r && v2l == v2r
    ValueLT v1l v2l == ValueLT v1r v2r         = v1l == v1r && v2l == v2r
    ValueLE v1l v2l == ValueLE v1r v2r         = v1l == v1r && v2l == v2r
    ValueEQ v1l v2l == ValueEQ v1r v2r         = v1l == v1r && v2l == v2r
    TrueObs  == TrueObs                        = True
    FalseObs == FalseObs                       = True
    _ == _                                     = False


instance Eq Action where
    {-# INLINABLE (==) #-}
    Deposit acc1 party1 tok1 val1 == Deposit acc2 party2 tok2 val2 =
        acc1 == acc2 && party1 == party2 && tok1 == tok2 && val1 == val2
    Choice cid1 bounds1 == Choice cid2 bounds2 =
        cid1 == cid2 && length bounds1 == length bounds2 && let
            bounds = zip bounds1 bounds2
            checkBound (Bound low1 high1, Bound low2 high2) = low1 == low2 && high1 == high2
            in all checkBound bounds
    Notify obs1 == Notify obs2 = obs1 == obs2
    _ == _ = False


instance Eq Contract where
    {-# INLINABLE (==) #-}
    Close == Close = True
    Pay acc1 payee1 tok1 value1 cont1 == Pay acc2 payee2 tok2 value2 cont2 =
        acc1 == acc2 && payee1 == payee2 && tok1 == tok2 && value1 == value2 && cont1 == cont2
    If obs1 cont1 cont2 == If obs2 cont3 cont4 =
        obs1 == obs2 && cont1 == cont3 && cont2 == cont4
    When cases1 timeout1 cont1 == When cases2 timeout2 cont2 =
        timeout1 == timeout2 && cont1 == cont2
        && length cases1 == length cases2
        && let cases = zip cases1 cases2
               checkCase (Case action1 cont1, Case action2 cont2) =
                    action1 == action2 && cont1 == cont2
           in all checkCase cases
    Let valId1 val1 cont1 == Let valId2 val2 cont2 =
        valId1 == valId2 && val1 == val2 && cont1 == cont2
    Assert obs1 cont1 == Assert obs2 cont2 = obs1 == obs2 && cont1 == cont2
    _ == _ = False


instance Eq State where
    {-# INLINABLE (==) #-}
    l == r = minSlot l == minSlot r
        && accounts l == accounts r
        && choices l == choices r
        && boundValues l == boundValues r

-- Lifting data types to Plutus Core
makeLift ''Party
makeIsDataIndexed ''Party [('PK,0),('Role,1)]
makeLift ''ChoiceId
makeIsDataIndexed ''ChoiceId [('ChoiceId,0)]
makeLift ''Token
makeIsDataIndexed ''Token [('Token,0)]
makeLift ''ValueId
makeIsDataIndexed ''ValueId [('ValueId,0)]
makeLift ''Value
makeIsDataIndexed ''Value [
    ('AvailableMoney,0),
    ('Constant,1),
    ('NegValue,2),
    ('AddValue,3),
    ('SubValue,4),
    ('MulValue,5),
    ('DivValue,12),
    ('Scale,6),
    ('ChoiceValue,7),
    ('SlotIntervalStart, 8),
    ('SlotIntervalEnd,9),
    ('UseValue,10),
    ('Cond,11)
    ]
makeLift ''Observation
makeIsDataIndexed ''Observation [
    ('AndObs,0),
    ('OrObs,1),
    ('NotObs,2),
    ('ChoseSomething,3),
    ('ValueGE,4),
    ('ValueGT,5),
    ('ValueLT,6),
    ('ValueLE,7),
    ('ValueEQ,8),
    ('TrueObs,9),
    ('FalseObs,10)
    ]
makeLift ''Bound
makeIsDataIndexed ''Bound [('Bound,0)]
makeLift ''Action
makeIsDataIndexed ''Action [('Deposit,0),('Choice,1),('Notify,2)]
makeLift ''Case
makeIsDataIndexed ''Case [('Case,0)]
makeLift ''Payee
makeIsDataIndexed ''Payee [('Account,0),('Party,1)]
makeLift ''Contract
makeIsDataIndexed ''Contract [
    ('Close,0),
    ('Pay,1),
    ('If,2),
    ('When,3),
    ('Let,4),
    ('Assert,5)
    ]
makeLift ''State
makeIsDataIndexed ''State [('State,0)]
makeLift ''Environment
makeLift ''Input
makeIsDataIndexed ''Input [('IDeposit,0),('IChoice,1),('INotify,2)]
