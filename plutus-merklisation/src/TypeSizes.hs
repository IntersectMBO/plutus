{- Perform various transformations on the ASTs for the validators of
   the sample contracts and print out a markdown table showing how
   these effect the size of the CBOR. -}

{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE NoImplicitPrelude  #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
--{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module TypeSizes (main) where


import qualified Prelude
import           Language.PlutusCore as PLC
import qualified Language.PlutusCore.Type                                      as PLC 
import qualified Language.PlutusCore.Name                                      as PLC 
import qualified Language.PlutusCore.CBOR                                      as PLC
import qualified Language.PlutusCore.Size                                      as PLC
import qualified Language.PlutusCore.Pretty                 as PLC

import           Language.PlutusCore.Merkle.Evaluation.CekMarker as CekMarker
import qualified Language.PlutusCore.Merkle.Merklise as M
import qualified Language.PlutusCore.Merkle.Constant.Typed                     as M
import qualified Language.PlutusCore.Merkle.Evaluation.Result                  as M
import qualified Language.PlutusCore.Merkle.CBOR                               as M
import qualified Language.PlutusCore.Merkle.Convert                            as M
import qualified Language.PlutusCore.Merkle.Merklisable                            as M
import qualified Language.PlutusCore.Merkle.Size                               as M
import qualified Language.PlutusCore.Merkle.Pretty                 as M
    
import qualified Language.PlutusCore.Interpreter.CekMachine                    as Cek1
import           Merkle
--import qualified Language.PlutusCore.Pretty                 as PLC

import           Language.PlutusTx.Coordination.Contracts.CrowdFunding         as Crowdfunding (exportedValidator)
import           Language.PlutusTx.Coordination.Contracts.Currency             as Currrency (exportedValidator)
import           Language.PlutusTx.Coordination.Contracts.Escrow               as Escrow (exportedValidator)
import           Language.PlutusTx.Coordination.Contracts.Future               as Future (exportedValidator)
import           Language.PlutusTx.Coordination.Contracts.Game                 as Game (exportedValidator)
import           Language.PlutusTx.Coordination.Contracts.GameStateMachine     as GameStateMachine (exportedValidator)
import           Language.PlutusTx.Coordination.Contracts.MultiSig             as MultiSig (exportedValidator)
import           Language.PlutusTx.Coordination.Contracts.MultiSigStateMachine as MultiSigStateMachine (exportedValidator)
import           Language.PlutusTx.Coordination.Contracts.PubKey               as PubKey (exportedValidator)
import           Language.PlutusTx.Coordination.Contracts.Swap                 as Swap (exportedValidator)
import           Language.PlutusTx.Coordination.Contracts.TokenAccount         as TokenAccount (exportedValidator)
import           Language.PlutusTx.Coordination.Contracts.Vesting              as Vesting (exportedValidator)

import qualified Language.PlutusTx.Evaluation as E
import qualified Language.PlutusTx.Builtins   as B
import           Language.PlutusTx.Prelude    hiding (Applicative (..))
import qualified Language.PlutusTx            as PlutusTx
import           Ledger                       (DataScript (..), Slot(..), PubKey, TxOutRef, RedeemerScript (..), ValidatorScript, scriptTxIn, scriptTxOut)
import qualified Ledger                       as Ledger
import qualified Ledger.Interval              as Interval
import qualified Ledger.Typed.Scripts         as Scripts
import           Ledger.Validation            (OracleValue (..), PendingTx, PendingTx' (..), PendingTxOut (..))
import qualified Ledger.Validation            as Validation
import qualified Ledger.Ada                   as Ada
import           Ledger.Ada                   (Ada)
import qualified Language.PlutusTx                                             as PlutusTx

import           Codec.CBOR.FlatTerm                                           (toFlatTerm)
import           Codec.Serialise                                               (deserialise, encode, serialise)
import qualified Data.ByteArray                                                as BA
import qualified Data.ByteString                                               as BSS
import qualified Data.ByteString.Lazy                                          as BSL
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text                                                     as T
import qualified Data.Text.IO                                                     as T
import           Data.Text.Encoding                                            (encodeUtf8)

import           Data.Word
import           Debug.Trace

import qualified Codec.CBOR.Write                                              as Write
import           Ledger.Scripts

import qualified Codec.Compression.GZip        as G

{----------------- Analysis -----------------}

import           Crypto.Hash


serialisedTypeSize :: Type TyName () -> Integer
serialisedTypeSize t =
{-    let digest  = merklise t :: Digest SHA256
        serialisedDigest :: BSL.ByteString = serialise digest
        typesize = BSL.length (serialise t)
        serdigsize = BSL.length serialisedDigest
    in trace ("Digest: " ++ show digest) $
       trace ("Serialised digest: " ++ show serialisedDigest ++ " (# " ++ show serdigsize ++ " bytes #)") $
-}
      toInteger . BSL.length . serialise $ t

getTypeSizes :: Term TyName Name () -> [Integer]
getTypeSizes t0 = gts t0 []
    where gts term l =
              case term of
                Var      {}           -> l
                TyAbs    _x _tn _k  t -> gts t l
                LamAbs   _x _n ty t   -> gts t (serialisedTypeSize ty : l)
                Apply    _x t1 t2     -> gts t2 (gts t1 l)
                Constant _x _c        -> l
                Builtin  _x _b        -> l
                TyInst   _x t ty      -> gts t (serialisedTypeSize ty : l)
                Unwrap   _x t         -> gts t l
                IWrap    _x ty1 ty2 t -> gts t (serialisedTypeSize ty2 : serialisedTypeSize ty1 : l)
                Error    _x ty        -> (serialisedTypeSize ty : l)

analyseTypes :: Program TyName Name () -> IO ()
analyseTypes (Program _ _ body)= do
  let sizes = getTypeSizes body
  mapM_ (putStrLn . show) sizes

analyseProg :: String -> PlutusTx.CompiledCode a -> IO ()
analyseProg name prg = do
  putStrLn name
  putStrLn ""
  analyseTypes $ PlutusTx.getPlc prg

dumpSerialisedProg :: PlutusTx.CompiledCode a -> IO ()
dumpSerialisedProg prg = do
  let v = serialise $ PlutusTx.getPlc prg
  BSL.putStr v
  return ()

dumpFlatTerm :: PlutusTx.CompiledCode a -> IO ()
dumpFlatTerm prg = do
  let v = toFlatTerm . encode $ PlutusTx.getPlc prg
  mapM_ (putStrLn . show) v

testSerialisation :: String -> PlutusTx.CompiledCode a -> IO ()
testSerialisation name prg = do
  putStr $ "Checking " ++ name ++ ": "
  let p = PlutusTx.getPlc prg
      s = serialise p
      q = deserialise s :: Program TyName Name ()
--  if p==q then putStrLn "OK" else putStrLn "Oh no!"
  return ()

printSeparator :: IO ()
printSeparator = putStrLn "\n----------------------------------------------------------------\n"

test :: IO()
test = do
  let h = hashString "This is a test" :: Digest SHA256
      l  :: [Word8] = [11,22,33,44,55,66,77,88,99,111,222]
      l2 :: [Int] = [11,22,33,44,55,66,77,88,99,111,222,333,555]
      bs :: BSS.ByteString = BSS.pack l
      s  :: BSL.ByteString = serialise h
      a  :: BA.Bytes = BA.pack l
      h' = deserialise s :: Digest SHA256
--        f = toFlatTerm $ s
  putStrLn ""
  putStrLn $ "hash of digest: " ++ show h
  putStrLn $ "serialised digest: " ++ show s
               ++ " (" ++ show (BSL.length s) ++ " bytes)"
  putStrLn $ "Serialised list 1: " ++ show (serialise l)
  putStrLn $ "Serialised list 2: " ++ show (serialise l2)
  putStrLn $ "Serialised bytestring: " ++ show (serialise bs)


hashString :: String -> Digest SHA256
hashString s  = hashWith SHA256 (encodeUtf8 $ T.pack s)

cborTest :: IO ()
cborTest = do
  putStrLn ""
  putStrLn . show $ toFlatTerm $ encode (4::Word8,"string"::String)
  putStrLn "----------"
  putStrLn . show $ toFlatTerm $ encode (4::Word8,())
  putStrLn "----------"
  putStrLn . show $ toFlatTerm $ encode ((),())
  putStrLn "----------"
  putStrLn . show $ toFlatTerm $ encode ()
  putStrLn "----------"
  putStrLn $ "(Word, Int): " ++ show (serialise (11::Word, 22::Int))
  putStrLn "----------"
  putStrLn $ "((),()): " ++ show (serialise ((),()))
  putStrLn "----------"
  putStrLn $ "(): " ++ show (serialise ())

validatorHash2 :: ValidatorScript -> ValidatorHash
validatorHash2 vl = ValidatorHash $ BSL.fromStrict $ BA.convert h' where
    h :: Digest SHA256 = hash $ Write.toStrictByteString e
    h' :: Digest SHA256 = hash h
    e = encode vl

hashCode :: ValidatorScript -> Digest SHA256
hashCode = undefined
-- hashCode = hash . BSL.fromStrict . BA.convert @SHA256
-- exportedValidator :: PlutusTx.CompiledCode (AccountOwner -> () -> V.PendingTx -> Bool)

addressTest :: IO ()
addressTest = do
  let currencySymbol = "f5280bdee70e27421f36798ffce5a21024d850f5604c9eb332442cffb56c57fe"
      cbor = serialise $ PlutusTx.getPlc TokenAccount.exportedValidator
      vs = encode $ fromCompiledCode (TokenAccount.exportedValidator)
  putStrLn $ "currencySymbol: " ++ currencySymbol
  putStrLn $ "hash:           " ++ "?" -- show (hash (encode vs))


{-# INLINABLE factri #-}
factri :: Integer -> Integer
factri n =
    if (n `B.remainderInteger` 2) `B.equalsInteger` 0
    then fac n
    else tri n
    where fac k = if k `B.lessThanEqInteger` 0
                  then 1
                  else k `B.multiplyInteger` (fac (k `B.subtractInteger` 1))
          tri k = if k `B.lessThanEqInteger` 0
                  then 0
                  else k `B.addInteger`  (tri (k `B.subtractInteger` 1))

vd1 :: Program TyName Name ()
vd1  = PlutusTx.getPlc $ $$(PlutusTx.compile [|| factri  20 ||])

vd2 :: Program TyName Name ()
vd2  = PlutusTx.getPlc $ $$(PlutusTx.compile [|| factri  21 ||])
-- Can we compile the application, or apply the compiled version dynamically?


numNodes :: PLC.Term PLC.TyName PLC.Name ann -> Int 
numNodes t =
    case t of
      PLC.Var      _ann _name          -> 1
      PLC.TyAbs    _ann _ty _kind body -> 1 Prelude.+ numNodes body
      PLC.LamAbs   _ann _ty _name body -> 1 Prelude.+ numNodes body
      PLC.Apply    _ann term1 term2    -> 1 Prelude.+ numNodes term1 Prelude.+ numNodes term2
      PLC.Constant _ann _cn            -> 1
      PLC.Builtin  _ann _bn            -> 1
      PLC.TyInst   _ann term _ty       -> 1 Prelude.+ numNodes term
      PLC.Unwrap   _ann term           -> 1 Prelude.+ numNodes term
      PLC.IWrap    _ann _ty1 _ty2 term -> 1 Prelude.+ numNodes term
      PLC.Error    _ann _ty            -> 1



printResult :: Either E.CekMachineException EvaluationResultDef -> IO ()
printResult r =
    case r of
      Left _ -> putStrLn "Error"
      Right v -> putStrLn $ show v

nodynamics :: M.DynamicBuiltinNameMeanings
nodynamics = M.DynamicBuiltinNameMeanings Map.empty

type NodeIDs = Set.Set Integer

getUsedNodes :: (Either CekMarker.CekMachineException M.EvaluationResultDef, NodeIDs) -> NodeIDs
getUsedNodes (e, nodes) =
    case e of
     Left _ -> error ()
     Right M.EvaluationFailure -> error()
     Right (M.EvaluationSuccess _term ) -> nodes
     
compress :: B.ByteString -> B.ByteString
compress = G.compressWith G.defaultCompressParams {G.compressLevel = G.bestCompression}

main :: IO ()
main = do
  let PLC.Program _ _ prog = vd2
      s1 = serialise vd1
      numberedProgram = M.numberProgram vd1
      PLC.Program _ _ numberedBody = numberedProgram
      usedNodes =  getUsedNodes $ CekMarker.evaluateCek nodynamics numberedBody
      prunedProgram = M.pruneProgram usedNodes numberedProgram
      s2 = serialise prunedProgram
      hash1 = M.merkleHash $ M.fromCoreProgram vd1
      hash2 = M.merkleHash prunedProgram
              
  putStrLn "Before Merklisation"
  putStrLn $ " Number of nodes: " ++ (show $ PLC.programSize vd1) ++ " (" ++ (show $ numNodes prog) ++ ")"
  putStrLn $ " Serialised size = " ++ (show $ BSL.length s1) ++ " bytes"
  putStrLn $ " Compressed size = " ++ (show $ BSL.length (compress s1)) ++ " bytes"
  putStrLn ""
  putStrLn "After Merklisation"
  putStrLn $ " Number of nodes used: " ++ (show $ Set.size usedNodes)
  putStrLn $ " Remaining nodes: " ++ (show $ M.programSize prunedProgram)
  putStrLn $ " Serialised size = " ++ (show $ BSL.length s2) ++ " bytes"
  putStrLn $ " Compressed size = " ++ (show $ BSL.length (compress s2)) ++ " bytes"
  putStrLn ""
  putStrLn $ "Merkle hash before pruning: " ++ (show $ hash1)
  putStrLn $ "Merkle hash after  pruning: " ++ (show $ hash2)

{- We only mark nodes which are touched by the evaluator.  This means that 
   types are never marked, so they are all Merklised away.  For the examples
   here, this reduces the number of nodes in the AST by a factor of about 3 
   (unused terms plus all types) and reduces the serialised size from 
   4892 bytes to 4070.  However, it increases the compressed size of the 
   serialised version from 1388 bytes to 2317 bytes, presumably because
   we now have incompressible hashes where we previously had compressible
   types.  Remember also that most types are pretty small: generate some
   histograms of the distribution of type sizes, and maybe the sizes of serialised types. }
           
{-
  putStr "\n\n==========================\n\n"
  T.putStrLn $ PLC.prettyPlcDefText vd2
  putStr "\n\n==========================\n\n"
  T.putStrLn $ M.prettyPlcDefText prunedProgram
-}           
    --  addressTest
--  dumpFlatTerm Future.exportedValidator
{-  let process = testSerialisation
  process    "Crowdfunding"         Crowdfunding.exportedValidator
  printSeparator
  process    "Currrency"            Currrency.exportedValidator
  printSeparator
  process    "Escrow"               Escrow.exportedValidator
  printSeparator
  process    "Future"               Future.exportedValidator
  printSeparator
  process    "Game"                 Game.exportedValidator
  printSeparator
  process    "GameStateMachine"     GameStateMachine.exportedValidator
  printSeparator
  process    "MultiSig"             MultiSig.exportedValidator
  printSeparator
  process    "MultiSigStateMachine" MultiSigStateMachine.exportedValidator
  printSeparator
  process    "PubKey"               PubKey.exportedValidator
  printSeparator
  process    "Swap"                 Swap.exportedValidator
  printSeparator
  process    "TokenAccount"         TokenAccount.exportedValidator
  printSeparator
  process    "Vesting"              Vesting.exportedValidator
-}
  -- Current validator is a little different for Future and PubKey

-- See plutus-use-cases/bench/Bench.hs for examples of manipulating PLC code
