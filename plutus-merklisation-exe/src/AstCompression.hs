{- Perform various transformations on the ASTs for the validators of
   the sample contracts and print out a markdown table showing how
   these effect the size of the CBOR. -}

{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

--{-# OPTIONS_GHC -fno-warn-unused-imports #-}
--{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
--{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module AstCompression (main) where

import qualified Language.PlutusCore                                           as PLC
import qualified Language.PlutusCore.CBOR                                      as PLC ()
--import qualified Language.PlutusCore.Pretty                 as PLC

import qualified Language.PlutusCore.Erasure.Untyped.CBOR                      as U ()
-- import qualified Language.PlutusCore.Untyped.Pretty         as U
import qualified Language.PlutusCore.Erasure.Untyped.Term                      as U

import qualified Language.PlutusCore.DeBruijn                                  as D

import qualified Language.PlutusCore.Merkle.CBOR                               as M ()

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

import qualified Codec.Compression.GZip                                        as G
import           Codec.Serialise                                               (serialise)
import           Control.Monad.Trans.Except                                    (runExceptT)
import qualified Data.ByteString.Lazy                                          as B
import           GHC.Int                                                       (Int64)
import           Numeric

{----------------- Analysis -----------------}

printHeader :: IO ()
printHeader = do
  putStrLn "| Contract | Compression | Typed | Typed, empty names | Untyped | Untyped, empty names | Untyped, no names | Untyped, de Bruijn |"
  putStrLn "| :---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"

printSeparator :: IO ()
printSeparator = do
  putStrLn "| |"  -- This is to separate entries in a table.  Two bars seems to be enough (but not one on GitHub).
  putStrLn "| |"  -- A thicker line or something would be better, but I don't think you can do that.

deBrProg :: PLC.Program PLC.TyName PLC.Name ann -> PLC.Program D.TyDeBruijn D.DeBruijn ann
deBrProg p =
   case runExceptT $ D.deBruijnProgram p of
     Left e -> error e
     Right y ->
         case y of
           Left freeVarError -> error ("Error: " ++ show freeVarError)
           Right t           -> t

data CompressionMode = Uncompressed | Compressed
data PrintFormat = Alone | WithPercentage

printEntry :: Int64 -> (B.ByteString, PrintFormat) -> CompressionMode -> IO ()
printEntry fullSize (s, mode) cmode = do
  let s' = case cmode of
             Uncompressed -> s
             Compressed   -> G.compressWith G.defaultCompressParams {G.compressLevel = G.bestCompression} s
  let len = B.length s'
  putStr . show $ len
  case mode of
    Alone -> pure ()
    WithPercentage ->
        putStr $ " (" ++ Numeric.showFFloat (Just 1) (percentage len) "%" ++ ")"
        where percentage n = 100.0 * (fromIntegral n) / (fromIntegral fullSize) :: Float

printInfo1 :: Int64 -> [(B.ByteString, PrintFormat)] -> CompressionMode -> IO ()
printInfo1 _fullSize [] _ = putStrLn ""
printInfo1 fullSize (i : rest) cmode = do
  printEntry fullSize i cmode
  putStr " | "
  printInfo1 fullSize rest cmode

printInfo :: Int64 -> [(B.ByteString, PrintFormat)] -> IO ()
printInfo fullSize entries = do
  putStr " Uncompressed | "
  printInfo1 fullSize entries Uncompressed
  putStr "|     | Compressed | "
  printInfo1 fullSize entries Compressed

analyseCompression :: String -> PLC.Program PLC.TyName PLC.Name () -> IO ()
analyseCompression name prog = do
  let s1 = serialise prog
      s2 = serialise $ U.anonProgram prog
      s3 = serialise $ U.eraseProgram prog
      s4 = serialise $ U.eraseProgram $ U.anonProgram prog
      s5 = serialise $ U.nameToIntProgram $ U.eraseProgram prog
      s6 = serialise $ U.deBruijnToIntProgram $ U.eraseProgram $ deBrProg prog
  putStr $ "| " ++ name ++ " | "
  printInfo (B.length s1) [(s1, Alone), (s2, Alone), (s3, Alone), (s4, Alone), (s5, WithPercentage), (s6, WithPercentage)]


analyseProg :: String -> CompiledCode a -> IO ()
analyseProg name prg = do
  analyseCompression name $ PlutusTx.getPlc prg


main :: IO ()
main = do
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

-- Current validator is a little different for Future and PubKey

-- See plutus-use-cases/bench/Bench.hs for examples of manipulating PLC code
