\documentclass[11pt,a4paper]{article}
\usepackage{tikz}
\usepackage[legalpaper,margin=1in]{geometry}
\usetikzlibrary{positioning}
%include polycode.fmt
\begin{document}

\begin{code}

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE FlexibleContexts    #-}
-- {-# LANGUAGE StrictData    #-} -- doesn't work yet with current Plutus Compiler
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS -fplugin=Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Marlowe.Compiler where
import           Control.Applicative        (Applicative (..))
import           Control.Monad              (Monad (..))
import           Control.Monad.Error.Class  (MonadError (..))
import           GHC.Generics               (Generic)
import qualified Data.Maybe                           as Maybe
import qualified Data.Set                           as Set
import Data.Set                           (Set)
import qualified Data.Map.Strict                           as Map
import Data.Map.Strict                           (Map)

import qualified Language.Plutus.CoreToPLC.Builtins as Builtins
import           Language.Plutus.Runtime    (PendingTxOutType(..), PendingTx(..), PendingTxIn(..),
                                            PendingTxOut(..), RedeemerHash, ValidatorHash, PubKey(..), Height,
                                            OracleValue (..), Signed(..))
import qualified Language.Plutus.Runtime    as Plutus
import           Language.Plutus.TH                 (plutus)
import           Wallet.API                 (EventTrigger (..), Range (..), WalletAPI (..), WalletAPIError, otherError,
                                             pubKey, signAndSubmit, payToPubKey, ownPubKeyTxOut)

import           Wallet.UTXO                        (Address', DataScript (..), TxOutRef', TxOut', TxOut(..), Validator (..), scriptTxIn,
                                                        scriptTxOut, applyScript, emptyValidator, unitData, txOutValue)
import qualified Wallet.UTXO                        as UTXO

import qualified Language.Plutus.Runtime.TH         as TH
import           Language.Plutus.Lift       (LiftPlc (..), TypeablePlc (..))
import           Prelude                            (Int, Integer, Bool (..), Num (..), Show(..), Read(..), Ord (..), Eq (..),
                    fromIntegral, succ, sum, ($), (<$>), (++), otherwise, Maybe(..))

\end{code}

\section{Marlowe}

Apparently, Plutus doesn't support complex recursive data types yet.


\begin{code}


data Contract = Null
              | CommitCash IdentCC PubKey Value Timeout Timeout
              | RedeemCC IdentCC
              | Pay IdentPay Person Person Value Timeout
                deriving (Eq, Generic)






\end{code}

\section{Assumptions}

\begin{itemize}
\item Fees are payed by transaction issues. For simplicity, assume zero fees.
\item PubKey is actually a hash of a public key
\item Every contract is created by contract owner by issuing a transaction with the contract in TxOut
\end{itemize}


\sectoin{Examples}

\begin{spec}
Alice = (PubKey 1)
Bob   = (PubKey 2)
value = (Value 100)
example = CommitCash (IdentCC 1) Alice value (Block 200) (Block 256)
            (Pay (IdentPay 1) Alice Bob value (Block 256) Null)
            Null
\end{spec}


\section{Questions}


Q: Should we put together the first CommitCash with the Contract setup? Contract setup would still require some money.

Q: Should we be able to return excess money in the contract (money not accounted for). To whom?
  We could use excess money to ensure a contract has money on it, and then return to the creator of the contract when it becomes Null.

Q: There is a risk someone will put a continuation of a Marlowe contract without getting the previous continuation as input.
  Can we detect this and allow for refund?

Q: What happens on a FailedPay? Should we still pay what we can?

Q: What is signed in a transaction?

Q: How to distinguish different instances of contracts? Is it a thing?
    Maybe we need to add a sort of identifier of a contract.



\begin{itemize}
\item Whole validator script (read Contract script) on every spending tx.
\item No offchain messages (`internal messages` in Ethereum)? How to call a function?
Answer: currently only via transaction
\end{itemize}


\section{Contract Initialization} \label{ContractInit}

This can be done in 2 ways.


\subsection{Initialization by depositing Ada to a new contract}

Just pay 1 Ada to a contract so that it becomes a part of UTXO.

\begin{tikzpicture}[
squarednode/.style={rectangle, draw=orange!60, fill=orange!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode] (commitcash) {TxIn Alice 1000};
\node[squarednode,align=center] (txOut1)       [right=of commitcash]
    {Contract\\value = 1\\dataScript = State \{\}};
\node[squarednode] (txOut2)       [below=of txOut1]
    {Change AliceAddr 999};

%Lines
\draw[->,thick] (commitcash.east) -- (txOut1.west);
\draw[->,thick] (commitcash.south) -- (txOut2.west);
\end{tikzpicture}


\par{Considerations}
Someone need to spend this 1 Ada/Lovelace, otherwise all Marlowe contracts will be in UTXO.
We can allow anyone to spend this value, so it'll become a part of a block reward. ???


\subsection{Initialization by CommitCash}

Any contract that starts with CommitCash can be initialized with actuall CommitCash

\begin{tikzpicture}[
squarednode/.style={rectangle, draw=orange!60, fill=orange!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode] (commitcash) {TxIn Alice 1000};
\node[squarednode,align=center] (txOut1)       [right=of commitcash]
    {Contract\\value = 100\\dataScript = State \{\\commits = [Committed #1 Alice v:100 t:256]\}};
\node[squarednode] (txOut2)       [below=of txOut1]
    {Change AliceAddr 900};

%Lines
\draw[->,thick] (commitcash.east) -- (txOut1.west);
\draw[->,thick] (commitcash.south) -- (txOut2.west);
\end{tikzpicture}



\section{Semantics}

Contract execution is a chain of transactions, where contract state is passed through \emph{dataScript},
and actions/inputs are passed as a \emph{redeemer} script and TxIns/TxOuts

Validation Script =  marlowe interpreter + possibly encoded address of a contract owner for initial deposit refund

This would change script address for every contract owner. This could be a desired or not desired property. Discuss.

redeemer script = action/input, i.e. CommitCash val timeout, Choice 1, OracleValue "oil" 20

pendingTx

dataScript = Contract + State

This implies that remaining Contract and its State are publicly visible. Discuss.


\subsection{Null}
Possibly allow redeem of cash spent by mistake on this address? How?

If we have all chain of txs of a contract we could allow redeems of mistakenly put money,
and that would allow a contract creator to withdraw the contract initialization payment. \ref{ContractInit}


\subsection{CommitCash}

Alice has 1000 ADA in AliceUTXO.

\begin{tikzpicture}[
squarednode/.style={rectangle, draw=orange!60, fill=orange!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode,align=center] (contract) {Contract\\redeemer = CC #1 v:100 t:256};
\node[squarednode] (commitcash)  [below=of contract]
    {TxIn Alice 1000};
\node[squarednode,align=center] (txOut1)       [right=of contract]
    {Contract'\\value = 100\\dataScript = State \{\\commits = [Committed #1 Alice v:100 t:256]\}};
\node[squarednode] (txOut2)       [below=of txOut1]
    {Change AliceAddr 900};

%Lines
\draw[->,thick] (contract.east) -- (txOut1.west);
\draw[->,thick] (commitcash.east) -- (txOut1.south);
\draw[->,thick] (commitcash.east) -- (txOut2.west);
\end{tikzpicture}


\subsection{RedeemCC}

Redeem a previously make CommitCash if valid.
Alice committed 100 ADA with CC 1, timeout 256.

\begin{tikzpicture}[
squarednode/.style={rectangle, draw=orange!60, fill=orange!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode,align=center] (contract) {Contract\\redeemer = RC 1};
\node[squarednode,align=center] (txOut1)       [right=of contract]
    {Contract'\\dataScript = State \{commits = []\}};
\node[squarednode] (txOut2)       [below=of txOut1]
    {Change AliceAddr 900};

%Lines
\draw[->,thick] (contract.east) -- (txOut1.west);
\draw[->,thick] (contract.east) -- (txOut2.west);
\end{tikzpicture}


\subsection{Pay}

Alice pays 100 ADA to Bob.

\begin{tikzpicture}[
squarednode/.style={rectangle, draw=orange!60, fill=orange!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode,align=center] (contract) {Contract\\redeemer = Pay AliceSignature BobAddress v:100};
\node[squarednode,align=center] (txOut1)       [right=of contract]
    {Contract'\\dataScript = State \{commits - payment\}};
\node[squarednode] (txOut2)       [below=of txOut1] {BobAddress 100};

%Lines
\draw[->,thick] (contract.east) -- (txOut1.west);
\draw[->,thick] (contract.south) -- (txOut2.west);
\end{tikzpicture}



\section{Types and Data Representation}


\subsection{Value}


Value is a set of contract primitives that represent constants,
functions, and variables that can be evaluated as an amount
of money.

\begin{code}


data Value = Committed IdentCC |
             Value Int |
            {-  AddValue Value Value |
             MulValue Value Value |
             DivValue Value Value Value | -- divident, divisor, default value (when divisor evaluates to 0) -}
             ValueFromChoice IdentChoice Person {- Value -} |
             ValueFromOracle PubKey {- Value -}
                    deriving (Eq, Generic)

instance LiftPlc Value
instance TypeablePlc Value



\end{code}


\begin{code}

type Timeout = Height
type Cash = Int

type Person      = PubKey


-- contractPlcCode = $(plutus [| CommitCash (IdentCC 1) (PubKey 1) 123 100 200 Null Null |])

-- Commitments, choices and payments are all identified by identifiers.
-- Their types are given here. In a more sophisticated model these would
-- be generated automatically (and so uniquely); here we simply assume that
-- they are unique.

newtype IdentCC = IdentCC Int
               deriving (Eq, Ord, Generic)
instance LiftPlc IdentCC
instance TypeablePlc IdentCC


newtype IdentChoice = IdentChoice { unIdentChoice :: Int }
               deriving (Eq, Ord, Generic)
instance LiftPlc IdentChoice
instance TypeablePlc IdentChoice

newtype IdentPay = IdentPay Int
               deriving (Eq, Ord, Generic)
instance LiftPlc IdentPay
instance TypeablePlc IdentPay


data InputCommand = Commit IdentCC
           | Payment IdentPay
           | Redeem IdentCC
           | SpendDeposit
           deriving (Generic)
instance LiftPlc InputCommand
instance TypeablePlc InputCommand

data Input = Input InputCommand [OracleValue Int] [(IdentChoice, ConcreteChoice)]
             deriving Generic
instance LiftPlc Input
instance TypeablePlc Input


data State = State {
                stateCommitted  :: [(IdentCC, CCStatus)]
                -- ^ commits MUST be sorted by expiration time, ascending
            } deriving (Eq, Ord, Generic)
instance LiftPlc State
instance TypeablePlc State


emptyState :: State
emptyState = State {stateCommitted = []}


data MarloweData = MarloweData {
        marloweState :: State,
        marloweContract :: Contract
    } deriving (Generic)
instance LiftPlc MarloweData
instance TypeablePlc MarloweData

type ConcreteChoice = Int

type CCStatus = (Person, CCRedeemStatus)

data CCRedeemStatus = NotRedeemed Cash Timeout
               deriving (Eq, Ord, Generic)
instance LiftPlc CCRedeemStatus
instance TypeablePlc CCRedeemStatus

instance LiftPlc Contract
instance TypeablePlc Contract
\end{code}



\section{Marlowe Interpreter and Helpers}

\begin{code}


marloweValidator :: Validator
marloweValidator = Validator result where
    result = UTXO.fromPlcCode $(plutus [| \ (Input input oracles choices :: Input) (MarloweData{..} :: MarloweData) (p@PendingTx{..} :: PendingTx ValidatorHash) -> let
        {-
            Marlowe Prelude
        -}
        eqPk :: PubKey -> PubKey -> Bool
        eqPk = $(TH.eqPubKey)

        eqValidator :: ValidatorHash -> ValidatorHash -> Bool
        eqValidator = $(TH.eqValidator)

        infixr 3 &&
        (&&) :: Bool -> Bool -> Bool
        (&&) = $(TH.and)

        infixr 3 ||
        (||) :: Bool -> Bool -> Bool
        (||) = $(TH.or)

        signedBy :: PubKey -> Bool
        signedBy = $(TH.txSignedBy) p

        reverse :: [a] -> [a]
        reverse l =  rev l [] where
                rev []     a = a
                rev (x:xs) a = rev xs (x:a)

        findCommit :: IdentCC -> [(IdentCC, CCStatus)] -> Maybe CCStatus
        findCommit i@(IdentCC searchId) commits = case commits of
            (IdentCC id, status) : _ | id == searchId -> Just status
            _ : xs -> findCommit i xs

        fromOracle :: PubKey -> Height -> [OracleValue Int] -> Int
        fromOracle pubKey blockNumber oracles = case oracles of
            OracleValue (Signed (pk, (bn, value))) : _ | pk `eqPk` pubKey && bn == blockNumber -> value
            _ : rest -> fromOracle pubKey blockNumber rest
            _ -> Builtins.error ()

        {-
            Marlowe Interpreter
        -}

        evalValue :: State -> Value -> Int
        evalValue (State committed) value = case value of
            Committed ident ->
                case findCommit ident committed of
                    Just (_, NotRedeemed c _) -> c
                    _ -> Builtins.error ()
            Value v -> v
            {- AddValue lhs rhs -> evalValue state os lhs + evalValue state os rhs
            MulValue lhs rhs -> evalValue state os lhs * evalValue state os rhs
            DivValue lhs rhs def -> do
                let divident = evalValue state os lhs
                let divisor  = evalValue state os rhs
                let defVal   = evalValue state os def
                if divisor == 0 then defVal else div divident divisor -}
            -- ValueFromChoice ident per {- def -} -> Maybe.fromMaybe (evalValue state (Value 0) {- FIXME should be def -}) (Map.lookup (ident, per) (sch state))
            ValueFromOracle pubKey -> fromOracle pubKey pendingTxBlockHeight oracles


        orderTxIns :: PendingTxIn -> PendingTxIn -> (PendingTxIn, PendingTxIn)
        orderTxIns t1 t2 = case t1 of
            PendingTxIn _ (Just _ :: Maybe (ValidatorHash, RedeemerHash)) _ -> (t1, t2)
            _ -> (t2, t1)

        step :: InputCommand -> State -> Contract -> (State, Contract, Bool)
        step input state contract = case input of
            Commit (IdentCC idCC) -> case contract of
                CommitCash (IdentCC expectedIdentCC) pubKey value startTimeout endTimeout -> let
                    PendingTx [in1, in2]
                        [PendingTxOut committed (Just (validatorHash, dataHash)) DataTxOut, out2]
                        _ _ blockNumber [committerSignature] thisScriptHash = p
                    (sIn@ (PendingTxIn _ _ scriptValue), commitTxIn@ (PendingTxIn _ _ commitValue)) = orderTxIns in1 in2
                    vv = evalValue state value
                    isValid = blockNumber <= startTimeout
                        && blockNumber <= endTimeout
                        && startTimeout < endTimeout -- I think it should be strongly bigger, otherwise I don't see the point
                        && vv > 0
                        && committed == vv + scriptValue
                        && expectedIdentCC == idCC
                        && signedBy pubKey
                        && validatorHash `eqValidator` thisScriptHash
                        -- TODO check hashes
                    in  if isValid then let
                            cns = (pubKey, NotRedeemed commitValue endTimeout)
                            con1 = Pay (IdentPay 1) (PubKey 2) (PubKey 1) (Committed (IdentCC 1)) 256
                            -- TODO insert respecting sort, commits MUST be sorted by expiration time
                            updatedState = case state of { State committed -> State ((IdentCC idCC, cns) : committed) }
                            in (updatedState, con1, True)
                        else Builtins.error ()
            Payment (IdentPay pid) -> case contract of
                Pay (IdentPay contractIdentPay) (from::Person) (to::Person) (payValue::Value) (timeout::Timeout) -> let
                    PendingTx [in1@ (PendingTxIn _ _ scriptValue)]
                        [PendingTxOut change (Just (validatorHash, dataHash)) DataTxOut, out2]
                        _ _ blockNumber [receiverSignature] thisScriptHash = p

                    calcAvailable :: Person -> Cash -> [(IdentCC, CCStatus)] -> Cash
                    calcAvailable from accum commits = case commits of
                        [] -> accum
                        (_, (party, NotRedeemed value expire)) : ls | from `eqPk` party && blockNumber <= expire -> let
                            in calcAvailable from (accum + value) ls

                    State committed = marloweState

                    -- | Note. It's O(nr_or_commitments), potentially slow. Check it last.
                    hasEnoughCommitted :: Person -> Cash -> Bool
                    hasEnoughCommitted from value = calcAvailable from 0 committed >= value

                    pv = evalValue state payValue

                    isValid = pid == contractIdentPay
                        && blockNumber <= timeout
                        && pv > 0
                        && change == scriptValue - pv
                        && signedBy to -- only receiver of the payment allowed to issue this transaction
                        && validatorHash `eqValidator` thisScriptHash
                        && hasEnoughCommitted from pv
                        -- TODO check inputs/outputs
                    in  if isValid then let
                            con1 = Null

                            -- Discounts the Cash from an initial segment of the list of pairs.

                            discountFromPairList :: Cash -> [(IdentCC, CCStatus)] -> [(IdentCC, CCStatus)]
                            discountFromPairList v ((ident, (p, NotRedeemed ve e)):t)
                                | v <= ve = [(ident, (p, NotRedeemed (ve - v) e))]
                                | ve < v = (ident, (p, NotRedeemed 0 e)) : discountFromPairList (v - ve) t
                            discountFromPairList _ (_:t) = t
                            discountFromPairList v []
                                | v == 0 = []
                                | otherwise = Builtins.error ()

                            updatedState = state --State (discountFromPairList payValue committed)
                            in (updatedState, con1, True)
                        else Builtins.error ()

            Redeem (IdentCC identCC) -> case contract of
                RedeemCC expectedIdentCC -> let
                    PendingTx [in1@ (PendingTxIn _ _ scriptValue)]
                        [PendingTxOut change (Just (validatorHash, dataHash)) DataTxOut, out2]
                        _ _ blockNumber [receiverSignature] thisScriptHash = p

                    State committed = marloweState

                    findAndRemove :: [(IdentCC, CCStatus)] -> [(IdentCC, CCStatus)] -> (Bool, State) -> (Bool, State)
                    findAndRemove ls resultCommits result = case ls of
                        (IdentCC i, (party, NotRedeemed val _)) : ls | i == identCC && change == scriptValue - val ->
                            findAndRemove ls resultCommits (True, state)
                        e@(i, (party, NotRedeemed val _)) : ls -> findAndRemove ls (e : resultCommits) result
                        [] -> let
                            (isValid, State commits) = result
                            in (isValid, State (reverse resultCommits))

                    (isValid, updatedState) = findAndRemove committed [] (False, state)

                    in if isValid then let
                        con1 = Null
                        in (updatedState, con1, True)
                    else Builtins.error ()
                _ -> let
                    PendingTx [in1@ (PendingTxIn _ _ scriptValue)]
                        [PendingTxOut change (Just (validatorHash, dataHash)) DataTxOut, out2]
                        _ _ blockNumber [receiverSignature] thisScriptHash = p

                    State committed = marloweState

                    findAndRemoveExpired :: [(IdentCC, CCStatus)] -> [(IdentCC, CCStatus)] -> (Bool, State) -> (Bool, State)
                    findAndRemoveExpired ls resultCommits result = case ls of
                        (IdentCC i, (party, NotRedeemed val expire)) : ls |
                            i == identCC && change == scriptValue - val && blockNumber >= expire ->
                                findAndRemoveExpired ls resultCommits (True, state)
                        e@(i, (party, NotRedeemed val _)) : ls -> findAndRemoveExpired ls (e : resultCommits) result
                        [] -> let
                            (isValid, State commits) = result
                            in (isValid, State (reverse resultCommits))

                    (isValid, updatedState) = findAndRemoveExpired committed [] (False, state)

                    in if isValid then let
                        con1 = Null
                        in (updatedState, con1, True)
                    else Builtins.error ()

            SpendDeposit -> case contract of
                Null -> (state, Null, True)

        (_::State, _::Contract, isValid) = step input marloweState marloweContract

        in if isValid then () else Builtins.error ()
        |])


createContract :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Contract
    -> Integer
    -> m ()
createContract contract value = do
    _ <- if value <= 0 then otherError "Must contribute a positive value" else pure ()
    let ds = DataScript $ UTXO.lifted MarloweData { marloweContract = contract, marloweState = emptyState }
    let v' = UTXO.Value $ fromIntegral value
    (payment, change) <- createPaymentWithChange v'
    let o = scriptTxOut v' marloweValidator ds

    signAndSubmit payment [o, change]


commitCash :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Person
    -> (TxOut', TxOutRef')
    -> Integer
    -> Timeout
    -> m ()
commitCash person (TxOut _ (UTXO.Value contractValue) _, ref) value timeout = do
    _ <- if value <= 0 then otherError "Must commit a positive value" else pure ()
    let identCC = (IdentCC 1)
    let input = Input (Commit identCC) [] []
    let i   = scriptTxIn ref marloweValidator (UTXO.Redeemer $ UTXO.lifted input)

    let ds = DataScript $ UTXO.lifted (MarloweData {
                marloweContract = Pay (IdentPay 1) (PubKey 2) (PubKey 1) (Committed (IdentCC 1)) 256,
                marloweState = State {stateCommitted=[(identCC, (person, NotRedeemed (fromIntegral value) timeout))]} })
    (payment, change) <- createPaymentWithChange (UTXO.Value value)
    let o = scriptTxOut (UTXO.Value $ value + contractValue) marloweValidator ds

    signAndSubmit (Set.insert i payment) [o, change]

commitCash2 :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Person
    -> (TxOut', TxOutRef')
    -> [OracleValue Int]
    -> Integer
    -> Timeout
    -> m ()
commitCash2 person (TxOut _ (UTXO.Value contractValue) _, ref) oracles value timeout = do
    _ <- if value <= 0 then otherError "Must commit a positive value" else pure ()
    let identCC = (IdentCC 1)
    let input = Input (Commit identCC) oracles []
    let i   = scriptTxIn ref marloweValidator (UTXO.Redeemer $ UTXO.lifted input)

    let ds = DataScript $ UTXO.lifted (MarloweData {
                marloweContract = Pay (IdentPay 1) (PubKey 2) (PubKey 1) (Committed (IdentCC 1)) 256,
                marloweState = State {stateCommitted=[(identCC, (person, NotRedeemed (fromIntegral value) timeout))]} })
    (payment, change) <- createPaymentWithChange (UTXO.Value value)
    let o = scriptTxOut (UTXO.Value $ value + contractValue) marloweValidator ds

    signAndSubmit (Set.insert i payment) [o, change]


receivePayment :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => (TxOut', TxOutRef')
    -> Integer
    -> Timeout
    -> m ()
receivePayment (TxOut _ (UTXO.Value contractValue) _, ref) value timeout = do
    _ <- if value <= 0 then otherError "Must commit a positive value" else pure ()
    let identPay = (IdentPay 1)
    let identCC = (IdentCC 1)
    let input = Input (Payment identPay) [] []
    let i   = scriptTxIn ref marloweValidator (UTXO.Redeemer $ UTXO.lifted input)

    let ds = DataScript $ UTXO.lifted (MarloweData {
                marloweContract = Null,
                marloweState = State {stateCommitted=[]} })
    let o = scriptTxOut (UTXO.Value $ contractValue - value) marloweValidator ds
    oo <- ownPubKeyTxOut (UTXO.Value value)

    signAndSubmit (Set.singleton i) [o, oo]

redeem :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => (TxOut', TxOutRef')
    -> IdentCC
    -> Integer
    -> m ()
redeem (TxOut _ (UTXO.Value contractValue) _, ref) identCC value = do
    _ <- if value <= 0 then otherError "Must commit a positive value" else pure ()
    let input = Input (Redeem identCC) [] []
    let i   = scriptTxIn ref marloweValidator (UTXO.Redeemer $ UTXO.lifted input)

    let ds = DataScript $ UTXO.lifted (MarloweData {
                marloweContract = Null,
                marloweState = State {stateCommitted=[]} })
    let o = scriptTxOut (UTXO.Value $ contractValue - value) marloweValidator ds
    oo <- ownPubKeyTxOut (UTXO.Value value)

    signAndSubmit (Set.singleton i) [o, oo]



endContract :: (Monad m, WalletAPI m) => (TxOut', TxOutRef') -> m ()
endContract (TxOut _ val _, ref) = do
    oo <- ownPubKeyTxOut val
    let scr = marloweValidator
    let input = Input SpendDeposit [] []
        i   = scriptTxIn ref scr $ UTXO.Redeemer $ UTXO.lifted input
    signAndSubmit (Set.singleton i) [oo]


\end{code}
\end{document}