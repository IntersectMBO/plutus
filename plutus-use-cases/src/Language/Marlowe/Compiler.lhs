\documentclass[11pt,a4paper]{article}
\usepackage{tikz}
\usepackage[legalpaper,margin=1in]{geometry}
\usetikzlibrary{positioning}
%include polycode.fmt
\begin{document}

\title {Marlowe: financial contracts on Cardano Computation Layer}
\author{Alexander Nemish}

\maketitle

\section{Introduction}

Here we present a reference implementation of Marlowe, domain-specific language targeted at
the execution of financial contracts in the style of Peyton Jones \emph{et al}
on Cardano Computation Layer.

The implementation is based on semantics described in paper
\emph{Marlowe: financial contracts on blockchain} by Simon Thompson and Pablo Lamela Seijas

We use PlutuxTx compiler, that compiles Haskell code into serialized \emph{Plutus Core} code,
to create a Cardano \emph{Validator Script} that secures value.

This \emph{Marlowe Validator Script} implements Marlowe interpreter, described in the paper.

\section{Extended UTXO model}
The \emph{extended UTxO model} brings a significant portion of the expressiveness of
Ethereum’s account-based scripting model to the UTxO-based Cardano blockchain.
The extension has two components: (1) an extension to the data carried by UTxO outputs
and processed by associated validator scripts together with
(2) an extension to the wallet backend to facilitate off-chain code
that coordinates the execution of on-chain computations.

\subsection{Extension to transaction outputs}
In the classic UTxO model (Cardano SL in Byron and Shelley),
a transaction output locked by a script carries two pieces of information:

\begin{itemize}
\item it’s value and
\item (the hash of) a validator script.
\end{itemize}

We extend this to include a second script, which we call the \emph{Data Script}.
This second script is a \emph{Plutus Core} expression, just like the \emph{Validator Script}.
However, the requirements on its type are different.
The type of the data script can be any monomorphic type.

\subsection{Extension to validator scripts}

An extended validator script expects four arguments:

\begin{itemize}
\item the redeemer expression,
\item the data script (from above),
\item the output’s value, and
\item parts of the validated transaction and related blockchain state. (More detail is in the next section.)
\end{itemize}

\begin{figure}[!h]
\centering
\begin{tikzpicture}[
squarednode/.style={rectangle, draw=blue!60, fill=blue!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode] (txout) {TxOut DataScript 1000};
\node[squarednode] (txin) [right=of txout] {RedeemerScript};
\node[squarednode] (pedningTx) [right=of txin] {PendingTx};
\node[squarednode,align=center] (script)       [below=of txin] {ValidatorScript};

%Lines
\draw[->,thick] (txout.south) -- (script.north);
\draw[->,thick] (txin.south) -- (script.north);
\draw[->,thick] (pedningTx.south) -- (script.north);
\end{tikzpicture}
\end{figure}

We consider a validator script to have executed successful
if it does not terminate in the \emph{Plutus Core} \emph{error} state.

\subsection{Blockchain state available to validator scripts}

Validator scripts receive, at a minimum, the following information from the validated transaction
and the rest of the blockchain:

\begin{itemize}
\item the current block height (not including the currently validated transaction),
\item the hash of the currently validated transaction,
\item for every input of the validated transaction, its value and the hashes of its validator, data, and redeemer scripts,
\item for every output of the validated transaction, its value and the hash of its validator and data script, and
\item the sum of the values of all unspent outputs (of the current blockchain without the currently validated transaction) locked by the currently executed validator script.
\end{itemize}




\section{Assumptions}

\begin{itemize}
\item Fees are payed by transaction issues. For simplicity, assume zero fees.
\item Every contract is created by contract owner by issuing a transaction with the contract in TxOut
\end{itemize}



\section{Semantics}

Marlowe Contract execution is a chain of transactions,
where remaining contract and its state is passed through \emph{Data Script},
and actions/inputs (i.e. \emph{Choices} and \emph{Oracle Values}) are passed as
\emph{Redeemer Script}

\emph{Validation Script} is always the same Marlowe interpreter implementation, available below.

Both \emph{Redeemer Script} and \emph{Data Script} have the same structure:
\begin{spec} (Input, MarloweData) \end{spec}

where
\begin{itemize}
\item \emph{Input} contains contract actions (i.e. \emph{Pay}, \emph{Redeem}), \emph{Choices} and \emph{Oracle Values},
\item \emph{MarloweData} contains remaining \emph{Contract} and its \emph{State}
\item \emph{State} is a set of \emph{Commits} plus set of made \emph{Choices}
\end{itemize}

To spend TxOut secured by Marlowe Validator Script, a user must provide \emph{Redeemer Script}
that is a tuple of an \emph{Input} and expected output of Marlowe Contract interpretation for
the given \emph{Input}, i.e. \emph{Contract} and \emph{State}.

To ensure that user provides valid remainig \emph{Contract} and \emph{State}
\emph{Marlowe Validator Script} compares evaluated contract and state with provided by user,
and rejects a transaction if those don't match.

To ensure that remaining contract's \emph{Data Script} has the same \emph{Contract} and \emph{State}
as was passed with \emph{Redeemer Script}, we check that \emph{Data Script} hash is
the same as \emph{Redeemer Script}.
That's why those are of the same structure \begin{spec} (Input, MarloweData) \end{spec}.

\begin{figure}[!h]
\centering
\begin{tikzpicture}[
squarednode/.style={rectangle, draw=red!60, fill=red!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode,align=center] (deposit) {Create};
\node[squarednode,align=center] (c1) [right=of deposit] {Contract};
\node[squarednode,align=center] (c2) [right=of c1] {Committed};
\node[squarednode,align=center] (c3) [right=of c2] {Payed};
\node[squarednode,align=center] (c4) [right=of c3] {Spend Deposit};
\node[squarednode] (commit) [below=of c1] {Alice Commit};
\node[squarednode] (pay) [below=of c3] {Bob Receives Payment};

%Lines
\draw[->,thick] (deposit.east) -- (c1.west);
\draw[->,thick] (c1.east) -- (c2.west);
\draw[->,thick] (c2.east) -- (c3.west);
\draw[->,thick] (c3.east) -- (c4.west);
\draw[->,thick] (commit.north) -- (c2.west);
\draw[->,thick] (c2.east) -- (pay.north);
\end{tikzpicture}
\end{figure}


\subsection{Commit}

Alice has 1000 Ada.

\begin{figure}[!h]
\centering
\begin{tikzpicture}[
squarednode/.style={rectangle, draw=orange!60, fill=orange!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode,align=center] (contract) {Contract\\Redeemer = Commit 100};
\node[squarednode] (commitcash)  [below=of contract]
    {TxIn Alice 1000};
\node[squarednode,align=center] (txOut1)       [right=of contract]
    {Contract'\\value = 100\\DataScript = [Committed Alice 100]};
\node[squarednode] (txOut2)       [below=of txOut1]
    {Change Alice 900};

%Lines
\draw[->,thick] (contract.east) -- (txOut1.west);
\draw[->,thick] (commitcash.east) -- (txOut1.south);
\draw[->,thick] (commitcash.east) -- (txOut2.west);
\end{tikzpicture}
\end{figure}

\subsection{Redeem}

Redeem a previously make CommitCash if valid.
Alice committed 100 Ada with CC 1, timeout 256.

\begin{figure}[!h]
\centering
\begin{tikzpicture}[
squarednode/.style={rectangle, draw=orange!60, fill=orange!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode,align=center] (contract) {Contract\\Redeemer = Redeem 1};
\node[squarednode,align=center] (txOut1)       [right=of contract]
    {Contract'\\DataScript = []};
\node[squarednode] (txOut2)       [below=of txOut1]
    {Change Alice 900};

%Lines
\draw[->,thick] (contract.east) -- (txOut1.west);
\draw[->,thick] (contract.east) -- (txOut2.west);
\end{tikzpicture}
\end{figure}

\subsection{Pay}

Alice pays 100 Ada to Bob.

\begin{figure}[!h]
\centering
\begin{tikzpicture}[
squarednode/.style={rectangle, draw=orange!60, fill=orange!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode,align=center] (contract) {Contract\\Redeemer = Pay Alice Bob 100};
\node[squarednode,align=center] (txOut1)       [right=of contract]
    {Contract'\\DataScript = [Committed Alice (v - 100)]};
\node[squarednode] (txOut2)       [below=of txOut1] {Bob 100};

%Lines
\draw[->,thick] (contract.east) -- (txOut1.west);
\draw[->,thick] (contract.south) -- (txOut2.west);
\end{tikzpicture}
\end{figure}


\subsection{SpendDeposit}

See \ref{ContractInit}

\section{Contract Initialization} \label{ContractInit}

This can be done in 2 ways.


\subsection{Initialization by depositing Ada to a new contract}

Just pay 1 Ada to a contract so that it becomes a part of \emph{eUTXO}.

\begin{figure}[!h]
\centering
\begin{tikzpicture}[
squarednode/.style={rectangle, draw=orange!60, fill=orange!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode] (commitcash) {TxIn Alice 1000};
\node[squarednode,align=center] (txOut1)       [right=of commitcash]
    {Contract\\value = 1};
\node[squarednode] (txOut2)       [below=of txOut1]
    {Change Alice 999};

%Lines
\draw[->,thick] (commitcash.east) -- (txOut1.west);
\draw[->,thick] (commitcash.south) -- (txOut2.west);
\end{tikzpicture}
\end{figure}


\par{Considerations}
Someone need to spend this 1 Ada, otherwise all Marlowe contracts will be in UTXO.
Current implementation allows anyone to spend this value.


\subsection{Initialization by CommitCash}

Any contract that starts with \emph{CommitCash} can be initialized with actuall \emph{CommitCash}

\begin{figure}[!h]
\centering
\begin{tikzpicture}[
squarednode/.style={rectangle, draw=orange!60, fill=orange!5, very thick, minimum size=10mm},
]
%Nodes
\node[squarednode] (commitcash) {TxIn Alice 1000};
\node[squarednode,align=center] (txOut1)       [right=of commitcash]
    {Contract\\value = 100\\DataScript [Committed Alice 100]};
\node[squarednode] (txOut2)       [below=of txOut1]
    {Change Alice 900};

%Lines
\draw[->,thick] (commitcash.east) -- (txOut1.west);
\draw[->,thick] (commitcash.south) -- (txOut2.west);
\end{tikzpicture}
\end{figure}


\section{Implementation}

\subsection{Imports}

\begin{code}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures  #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE RankNTypes   #-}
{-# LANGUAGE NamedFieldPuns   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS -fplugin=Language.PlutusTx.Plugin
    -fplugin-opt Language.PlutusTx.Plugin:dont-typecheck #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns -Wno-name-shadowing #-}

module Language.Marlowe.Compiler where
import           Control.Applicative            ( Applicative(..) )
import           Control.Monad                  ( Monad(..)
                                                , void
                                                )
import           Control.Monad.Error.Class      ( MonadError(..) )
import           Data.Maybe                     (maybeToList)
import qualified Data.Set                       as Set

import qualified Language.PlutusTx              as PlutusTx
import           Wallet                         ( WalletAPI(..)
                                                , WalletAPIError
                                                , throwOtherError
                                                , signAndSubmit
                                                , ownPubKeyTxOut
                                                )

import           Ledger                         ( DataScript(..)
                                                , Height(..)
                                                , PubKey(..)
                                                , TxOutRef'
                                                , TxOut'
                                                , TxIn'
                                                , TxOut(..)
                                                , ValidatorScript(..)
                                                , scriptTxIn
                                                , scriptTxOut
                                                )
import qualified Ledger                         as Ledger
import Ledger.Validation
import qualified Ledger.Validation            as Validation
import qualified Language.PlutusTx.Builtins     as Builtins
import           Language.PlutusTx.Lift         ( makeLift )
import Language.Marlowe.Common


\end{code}

\subsection{Types and Data Representation}




\subsection{Identifiers}

Commitments, choices and payments are all identified by identifiers.
Their types are given here. In a more sophisticated model these would
be generated automatically (and so uniquely); here we simply assume that
they are unique.


\subsection{Input}

Input is passed in \emph{Redeemer Script}

\begin{code}

\end{code}

\subsection{Contract State}

Commits MUST be sorted by expiration time, ascending.

\begin{code}



emptyState :: State
emptyState = State { stateCommitted = [], stateChoices = [] }

\end{code}


\subsection{Value}


Value is a set of contract primitives that represent constants,
functions, and variables that can be evaluated as an amount
of money.

\begin{code}


\end{code}

\subsection{Observation}

Representation of observations over observables and the state.
Rendered into predicates by interpretObs.

\begin{code}
\end{code}

\subsection{Marlowe Contract Data Type}
\subsection{Marlowe Data Script}

This data type is a content of a contract \emph{Data Script}

\begin{code}

data MarloweData = MarloweData {
        marloweState :: State,
        marloweContract :: Contract
    }
makeLift ''MarloweData

\end{code}



\section{Marlowe Validator Script}


\emph{Validator Script} is a serialized Plutus Core generated by Plutus Compiler via Template Haskell.

\begin{code}

marloweValidator :: ValidatorScript
marloweValidator = ValidatorScript result where
    result = Ledger.fromCompiledCode $$(PlutusTx.compile [|| \
        (input@(Input _ _ inputChoices :: Input), MarloweData expectedState expectedContract)
        (_ :: Input, MarloweData{..} :: MarloweData)
        (pendingTx@ PendingTx{ pendingTxBlockHeight } :: PendingTx ValidatorHash) -> let

        eqPk :: PubKey -> PubKey -> Bool
        eqPk = $$(Validation.eqPubKey)

        eqIdentCC :: IdentCC -> IdentCC -> Bool
        eqIdentCC (IdentCC a) (IdentCC b) = a == b

        not :: Bool -> Bool
        not = $$(PlutusTx.not)

        infixr 3 &&
        (&&) :: Bool -> Bool -> Bool
        (&&) = $$(PlutusTx.and)

        infixr 3 ||
        (||) :: Bool -> Bool -> Bool
        (||) = $$(PlutusTx.or)

        null :: [a] -> Bool
        null [] = True
        null _  = False

        reverse :: [a] -> [a]
        reverse l =  rev l [] where
                rev []     a = a
                rev (x:xs) a = rev xs (x:a)

        -- it's quadratic, I know. We'll have Sets later
        mergeChoices :: [Choice] -> [Choice] -> [Choice]
        mergeChoices input choices = case input of
            choice : rest | notElem eqChoice choices choice -> mergeChoices rest (choice : choices)
                          | otherwise -> mergeChoices rest choices
            [] -> choices
          where
            eqChoice :: Choice -> Choice -> Bool
            eqChoice ((IdentChoice id1, p1), _) ((IdentChoice id2, p2), _) = id1 == id2 && p1 `eqPk` p2


        eqValue :: Value -> Value -> Bool
        eqValue = $$(equalValue)

        eqObservation :: Observation -> Observation -> Bool
        eqObservation = $$(equalObservation) eqValue

        eqContract :: Contract -> Contract -> Bool
        eqContract = $$(equalContract) eqValue eqObservation

        all :: () -> forall a. (a -> a -> Bool) -> [a] -> [a] -> Bool
        all _ = go where
            go _ [] [] = True
            go eq (a : as) (b : bs) = eq a b && all () eq as bs
            go _ _ _ = False

        eqCommit :: Commit -> Commit -> Bool
        eqCommit (id1, (pk1, (NotRedeemed val1 t1))) (id2, (pk2, (NotRedeemed val2 t2))) =
            id1 `eqIdentCC` id2 && pk1 `eqPk` pk2 && val1 == val2 && t1 == t2

        eqChoice :: Choice -> Choice -> Bool
        eqChoice ((IdentChoice id1, pk1), c1) ((IdentChoice id2, pk2), c2) =
            id1 == id2 && c1 == c2 && pk1 `eqPk` pk2

        eqState :: State -> State -> Bool
        eqState (State commits1 choices1) (State commits2 choices2) =
            all () eqCommit commits1 commits2 && all () eqChoice choices1 choices2

        elem :: (a -> a -> Bool) -> [a] -> a -> Bool
        elem = realElem
          where
            realElem eq (e : ls) a = a `eq` e || realElem eq ls a
            realElem _ [] _ = False

        notElem :: (a -> a -> Bool) -> [a] -> a -> Bool
        notElem eq as a = not (elem eq as a)

        validateContract :: ValidatorState -> Contract -> (ValidatorState, Bool)
        validateContract = $$(validateContractQ)

        currentBlockNumber :: Int
        currentBlockNumber = let Height blockNumber = pendingTxBlockHeight in blockNumber

        eval :: Input -> Int -> PendingTx' -> State -> Contract -> (State, Contract, Bool)
        eval = $$(evaluateContract)

        (_, contractIsValid) = validateContract (ValidatorState [] []) marloweContract

        State currentCommits currentChoices = marloweState

        in if contractIsValid then let
            -- record Choices from Input into State
            mergedChoices = mergeChoices (reverse inputChoices) currentChoices

            stateWithChoices = State currentCommits mergedChoices

            (newState::State, newCont::Contract, validated) =
                eval input currentBlockNumber pendingTx stateWithChoices marloweContract

            allowTransaction = validated
                && newCont `eqContract` expectedContract
                && newState `eqState` expectedState

            in if allowTransaction then () else Builtins.error ()
        else if null currentCommits then () else Builtins.error ()
        ||])

\end{code}
\subsection{Marlowe Wallet API}
\begin{code}


createContract :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => Contract
    -> Int
    -> m ()
createContract contract value = do
    _ <- if value <= 0 then throwOtherError "Must contribute a positive value" else pure ()
    let ds = DataScript $ Ledger.lifted (Input SpendDeposit [] [], MarloweData {
            marloweContract = contract,
            marloweState = emptyState })
    let v' = Ledger.Value value
    (payment, change) <- createPaymentWithChange v'
    let o = scriptTxOut v' marloweValidator ds

    void $ signAndSubmit payment (o : maybeToList change)



marloweTx ::
    (Input, MarloweData)
    -> (TxOut', TxOutRef')
    -> (TxIn' -> (Int -> TxOut') -> Int -> m ())
    -> m ()
marloweTx inputState txOut f = do
    let (TxOut _ (Ledger.Value contractValue) _, ref) = txOut
    let lifted = Ledger.lifted inputState
    let scriptIn = scriptTxIn ref marloweValidator $ Ledger.RedeemerScript lifted
    let dataScript = DataScript lifted
    let scritOut v = scriptTxOut (Ledger.Value v) marloweValidator dataScript
    f scriptIn scritOut contractValue


createRedeemer
    :: InputCommand -> [OracleValue Int] -> [Choice] -> State -> Contract -> (Input, MarloweData)
createRedeemer inputCommand oracles choices expectedState expectedCont =
    let input = Input inputCommand oracles choices
        mdata = MarloweData { marloweContract = expectedCont, marloweState = expectedState }
    in  (input, mdata)

commit :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => (TxOut', TxOutRef')
    -> [OracleValue Int]
    -> [Choice]
    -> IdentCC
    -> Int
    -> State
    -> Contract
    -> m ()
commit txOut oracles choices identCC value expectedState expectedCont = do
    _ <- if value <= 0 then throwOtherError "Must commit a positive value" else pure ()
    let redeemer = createRedeemer (Commit identCC) oracles choices expectedState expectedCont
    marloweTx redeemer txOut $ \ i getOut v -> do
        (payment, change) <- createPaymentWithChange (Ledger.Value value)
        void $ signAndSubmit (Set.insert i payment) (getOut (v + value) : maybeToList change)


receivePayment :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => (TxOut', TxOutRef')
    -> [OracleValue Int]
    -> [Choice]
    -> IdentPay
    -> Int
    -> State
    -> Contract
    -> m ()
receivePayment txOut oracles choices identPay value expectedState expectedCont = do
    _ <- if value <= 0 then throwOtherError "Must commit a positive value" else pure ()
    let redeemer = createRedeemer (Payment identPay) oracles choices expectedState expectedCont
    marloweTx redeemer txOut $ \ i getOut v -> do
        let out = getOut (v - value)
        oo <- ownPubKeyTxOut (Ledger.Value value)
        void $ signAndSubmit (Set.singleton i) [out, oo]


redeem :: (
    MonadError WalletAPIError m,
    WalletAPI m)
    => (TxOut', TxOutRef')
    -> [OracleValue Int]
    -> [Choice]
    -> IdentCC
    -> Int
    -> State
    -> Contract
    -> m ()
redeem txOut oracles choices identCC value expectedState expectedCont = do
    _ <- if value <= 0 then throwOtherError "Must commit a positive value" else pure ()
    let redeemer = createRedeemer (Redeem identCC) oracles choices expectedState expectedCont
    marloweTx redeemer txOut $ \ i getOut v -> do
        let out = getOut (v - value)
        oo <- ownPubKeyTxOut (Ledger.Value value)
        void $ signAndSubmit (Set.singleton i) [out, oo]



endContract :: (Monad m, WalletAPI m) => (TxOut', TxOutRef') -> State -> m ()
endContract txOut state = do
    let redeemer = createRedeemer SpendDeposit [] [] state Null
    marloweTx redeemer txOut $ \ i _ v -> do
        oo <- ownPubKeyTxOut (Ledger.Value v)
        void $ signAndSubmit (Set.singleton i) [oo]

\end{code}
\end{document}
