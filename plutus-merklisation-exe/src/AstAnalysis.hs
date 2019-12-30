{- Load the ASTs for the validators of the sample contracts and print
   out a markdown table showing how many of each type of node there
   are, and what percentage of the total number of nodes these make
   up. Also print out a second table showing depths of entire AST and
   depth of nesting of Lams. -}

{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

--{-# OPTIONS_GHC -fno-warn-unused-imports #-}
--{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
--{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module AstAnalysis (main) where

import qualified Language.PlutusCore                                           as PLC

import           Language.PlutusTx.Coordination.Contracts.Crowdfunding         as Crowdfunding
import           Language.PlutusTx.Coordination.Contracts.Currency             as Currrency
import           Language.PlutusTx.Coordination.Contracts.Escrow               as Escrow
import           Language.PlutusTx.Coordination.Contracts.Future               as Future
import           Language.PlutusTx.Coordination.Contracts.Game                 as Game
import           Language.PlutusTx.Coordination.Contracts.GameStateMachine     as GameStateMachine
import           Language.PlutusTx.Coordination.Contracts.MultiSig             as MultiSig
import           Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine as MultiSigStateMachine
import           Language.PlutusTx.Coordination.Contracts.PubKey               as PubKey
import           Language.PlutusTx.Coordination.Contracts.Swap                 as Swap
import           Language.PlutusTx.Coordination.Contracts.TokenAccount         as TokenAccount
import           Language.PlutusTx.Coordination.Contracts.Vesting              as Vesting

import           Language.PlutusTx                                             as PlutusTx

import           Control.Lens
import           Numeric

data TermCounts =
    TermCounts {
      _varcount :: Int,
      _abscount :: Int,
      _lamcount :: Int,
      _appcount :: Int,
      _concount :: Int,
      _bincount :: Int,
      _tyicount :: Int,
      _unwcount :: Int,
      _wrpcount :: Int,
      _errcount :: Int,
      _namcount :: Int
    }

makeLenses ''TermCounts

{----------------- Analysis -----------------}

emptyCounts :: TermCounts
emptyCounts = TermCounts 0 0 0 0 0 0 0 0 0 0 0

totalNodes :: TermCounts -> Int
totalNodes c = _varcount c + _abscount c + _lamcount c + _appcount c + _concount c
               + _bincount c + _tyicount c + _unwcount c + _wrpcount c + _errcount c

printHeader :: IO ()
printHeader = do
  putStrLn "| Contract | Total Nodes | Var | Lam | App | Constant | Builtin | Error | TyAbs | TyInst | Wrap | Unwrap | (Names) |"
  putStrLn "| :---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: |"

printCounts :: String -> TermCounts -> IO ()
printCounts filename c = do
  let tot = totalNodes c
      percentage n = 100.0 * (fromIntegral n) / (fromIntegral tot) :: Float
      prp x = putStr $ Numeric.showFFloat (Just 1) (percentage x) "%"
      pr = putStr . show
  putStr  "| "
  putStr filename
  putStr  " | "
  pr $ tot
  putStr  " | "
  pr $ _varcount c
  putStr  " | "
  pr $ _lamcount c
  putStr  " | "
  pr $ _appcount c
  putStr  " | "
  pr $ _concount c
  putStr  " | "
  pr $ _bincount c
  putStr  " | "
  pr $ _errcount c
  putStr  " | "
  pr $ _abscount c
  putStr  " | "
  pr $ _tyicount c
  putStr  " | "
  pr $ _wrpcount c
  putStr  " | "
  pr $ _unwcount c
  putStr  " | ("
  pr $ _namcount c
  putStr  ")| "
  putStrLn ""
  putStr "|       |       |"
  prp $ _varcount c
  putStr  " | "
  prp $ _lamcount c
  putStr  " | "
  prp $ _appcount c
  putStr  " | "
  prp $ _concount c
  putStr  " | "
  prp $ _bincount c
  putStr  " | "
  prp $ _errcount c
  putStr  " | "
  prp $ _abscount c
  putStr  " | "
  prp $ _tyicount c
  putStr  " | "
  prp $ _wrpcount c
  putStr  " | "
  prp $ _unwcount c
  putStr  " | - | "
  putStrLn ""

printSeparator :: IO ()
printSeparator = do
  putStrLn "| |"  -- This is to separate entries in a table.  Two bars (but on GitHub, not one) seem to be enough.
  putStrLn "| |"  -- A thicker line or something would be better, but I don't think you can do that.

freqTerm :: PLC.Term PLC.TyName PLC.Name ann -> TermCounts -> TermCounts
freqTerm t counts =
    case t of
      PLC.Var      _ann _name          -> counts & varcount +~ 1 & namcount +~ 1
      PLC.TyAbs    _ann _ty _kind body -> freqTerm body (counts & abscount +~ 1)
      PLC.LamAbs   _ann _ty _name body -> freqTerm body (counts & lamcount +~ 1 & namcount +~ 1)
      PLC.Apply    _ann term1 term2    -> freqTerm term2 (freqTerm term1 (counts & appcount +~ 1))
      PLC.Constant _ann _cn            -> counts & concount +~ 1
      PLC.Builtin  _ann _bn            -> counts & bincount +~ 1
      PLC.TyInst   _ann term _ty       -> freqTerm term (counts & tyicount +~ 1)
      PLC.Unwrap   _ann term           -> freqTerm term (counts & unwcount +~ 1)
      PLC.IWrap    _ann _ty1 _ty2 term -> freqTerm term (counts & wrpcount +~ 1)
      PLC.Error    _ann _ty            -> counts & errcount +~ 1

freqProg :: PLC.Program PLC.TyName PLC.Name ann -> TermCounts
freqProg (PLC.Program _ver _ty body) = freqTerm body emptyCounts

analyseProg :: String -> CompiledCode a -> IO ()
analyseProg name prg = do
  let counts = freqProg $ PlutusTx.getPlc prg
  printCounts name counts

printTermCounts :: IO ()
printTermCounts = do
  printHeader
  analyseProg    "Crowdfunding"         Crowdfunding.exportedValidator
  printSeparator
  analyseProg    "Currrency"            Currrency.exportedValidator
  printSeparator
  analyseProg    "Escrow"               Escrow.exportedValidator
  printSeparator
  analyseProg    "Future"               Future.exportedValidator
  printSeparator
  analyseProg    "Game"                 Game.exportedValidator
  printSeparator
  analyseProg    "GameStateMachine"     GameStateMachine.exportedValidator
  printSeparator
  analyseProg    "MultiSig"             MultiSig.exportedValidator
  printSeparator
  analyseProg    "MultiSigStateMachine" MultiSigStateMachine.exportedValidator
  printSeparator
  analyseProg    "PubKey"               PubKey.exportedValidator
  printSeparator
  analyseProg    "Swap"                 Swap.exportedValidator
  printSeparator
  analyseProg    "TokenAccount"         TokenAccount.exportedValidator
  printSeparator
  analyseProg    "Vesting"              Vesting.exportedValidator


---------------- Depth of ASTs ----------------

termDepth :: PLC.Term PLC.TyName PLC.Name ann -> Integer
termDepth t =
    case t of
      PLC.Var      _ann _name          -> 1
      PLC.TyAbs    _ann _ty _kind body -> 1 + termDepth body
      PLC.LamAbs   _ann _ty _name body -> 1 + termDepth body
      PLC.Apply    _ann term1 term2    -> 1 + max (termDepth term1) (termDepth term2)
      PLC.Constant _ann _cn            -> 1
      PLC.Builtin  _ann _bn            -> 1
      PLC.TyInst   _ann term _ty       -> 1 + termDepth term
      PLC.Unwrap   _ann term           -> 1 + termDepth term
      PLC.IWrap    _ann _ty1 _ty2 term -> 1 + termDepth term
      PLC.Error    _ann _ty            -> 1


-- Total number of nodes in AST.  We've already got this in the first table anyway.

numNodes :: PLC.Term PLC.TyName PLC.Name ann -> Int
numNodes t =
    case t of
      PLC.Var      _ann _name          -> 1
      PLC.TyAbs    _ann _ty _kind body -> 1 + numNodes body
      PLC.LamAbs   _ann _ty _name body -> 1 + numNodes body
      PLC.Apply    _ann term1 term2    -> 1 + numNodes term1 + numNodes term2
      PLC.Constant _ann _cn            -> 1
      PLC.Builtin  _ann _bn            -> 1
      PLC.TyInst   _ann term _ty       -> 1 + numNodes term
      PLC.Unwrap   _ann term           -> 1 + numNodes term
      PLC.IWrap    _ann _ty1 _ty2 term -> 1 + numNodes term
      PLC.Error    _ann _ty            -> 1




-- "Lambda depth" of AST's: depth of Lam nesting

termLDepth :: PLC.Term PLC.TyName PLC.Name ann -> Integer
termLDepth t =
    case t of
      PLC.Var      _ann _name          -> 0
      PLC.TyAbs    _ann _ty _kind body -> termLDepth body
      PLC.LamAbs   _ann _ty _name body -> 1 + termLDepth body
      PLC.Apply    _ann term1 term2    -> max (termLDepth term1) (termLDepth term2)
      PLC.Constant _ann _cn            -> 0
      PLC.Builtin  _ann _bn            -> 0
      PLC.TyInst   _ann term _ty       -> termLDepth term
      PLC.Unwrap   _ann term           -> termLDepth term
      PLC.IWrap    _ann _ty1 _ty2 term -> termLDepth term
      PLC.Error    _ann _ty            -> 0

printDepthHeader :: IO()
printDepthHeader = do
  putStrLn "| Contract | Total Nodes | Depth | &lambda;-depth |"
  putStrLn "| :---: | ---: | ---: | ---: |"

printDepths :: String -> CompiledCode ann -> IO ()
printDepths name validator = do
  let PLC.Program _ver _ty body = PlutusTx.getPlc validator
  putStr "| "
  putStr name
  putStr " | "
  putStr $ show (numNodes body)
  putStr " | "
  putStr $ show (termDepth body)
  putStr " | "
  putStr $ show (termLDepth body)
  putStrLn " |"

printValidatorDepths :: IO ()
printValidatorDepths = do
  printDepthHeader
  printDepths    "Crowdfunding"         Crowdfunding.exportedValidator
  printDepths    "Currrency"            Currrency.exportedValidator
  printDepths    "Escrow"               Escrow.exportedValidator
  printDepths    "Future"               Future.exportedValidator
  printDepths    "Game"                 Game.exportedValidator
  printDepths    "GameStateMachine"     GameStateMachine.exportedValidator
  printDepths    "MultiSig"             MultiSig.exportedValidator
  printDepths    "MultiSigStateMachine" MultiSigStateMachine.exportedValidator
  printDepths    "PubKey"               PubKey.exportedValidator
  printDepths    "Swap"                 Swap.exportedValidator
  printDepths    "TokenAccount"         TokenAccount.exportedValidator
  printDepths    "Vesting"              Vesting.exportedValidator


---------------- Main ----------------

main :: IO ()
main = do
  printTermCounts
  putStrLn ""
  putStrLn ""
  printValidatorDepths

-- Current validator is a little different for Future and PubKey

-- See plutus-use-cases/bench/Bench.hs for examples of manipulating PLC code
