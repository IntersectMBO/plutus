{- Perform various transformations on the ASTs for the validators of
   the sample contracts and print out a markdown table showing how
   these effect the size of the CBOR. -}

{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module TypeSizes (main) where

import qualified Prelude

import qualified Language.PlutusCore                                           as P hiding (serialisedSize)
import qualified Language.PlutusCore.CBOR                                      as P
import qualified Language.PlutusCore.Name                                      as P
import qualified Language.PlutusCore.Pretty                                    as P

import qualified Language.PlutusCore.Merkle.CBOR                               as M
import qualified Language.PlutusCore.Merkle.Constant.Typed                     as M
import qualified Language.PlutusCore.Merkle.Convert                            as M
import           Language.PlutusCore.Merkle.Evaluation.CekMarker               as CekMarker
import qualified Language.PlutusCore.Merkle.Evaluation.Result                  as M
import qualified Language.PlutusCore.Merkle.Merklisable                        as M
import qualified Language.PlutusCore.Merkle.Merklise                           as M
import qualified Language.PlutusCore.Merkle.PLCSize                            as PLCSize
import qualified Language.PlutusCore.Merkle.Size                               as M

import qualified Language.PlutusTx                                             as PlutusTx
import qualified Language.PlutusTx                                             as PlutusTx
import qualified Language.PlutusTx.Builtins                                    as B
import qualified Language.PlutusTx.Evaluation                                  as E
import           Language.PlutusTx.Prelude                                     hiding (Applicative (..))

import           Language.PlutusTx.Coordination.Contracts.Crowdfunding         as Crowdfunding (exportedValidator)
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

import qualified Codec.Compression.GZip                                        as G
import           Ledger.Scripts

import           Codec.CBOR.FlatTerm                                           (toFlatTerm)
import qualified Codec.CBOR.Write                                              as Write
import           Codec.Serialise                                               (Serialise, deserialise, encode,
                                                                                serialise)
import           Crypto.Hash

import qualified Data.ByteArray                                                as BA
import qualified Data.ByteString                                               as BSS
import qualified Data.ByteString.Lazy                                          as BSL
import qualified Data.Map                                                      as Map
import qualified Data.Set                                                      as Set
import qualified Data.Text                                                     as T
import           Data.Text.Encoding                                            (encodeUtf8)
import qualified Data.Text.IO                                                  as T

import           Data.Word



{----------------- Analysis -----------------}


serialisedSize :: Serialise a => a -> Integer
serialisedSize t =
{-    let digest  = merklise t :: Digest SHA256
        serialisedDigest :: BSL.ByteString = serialise digest
        typesize = BSL.length (serialise t)
        serdigsize = BSL.length serialisedDigest
    in trace ("Digest: " ++ show digest) $
       trace ("Serialised digest: " ++ show serialisedDigest ++ " (# " ++ show serdigsize ++ " bytes #)") $
-}
      toInteger . BSL.length . serialise $ t

getTypeSizes :: P.Term P.TyName P.Name () -> [(Integer, Integer)]
getTypeSizes t0 = loop t0 []
    where loop term l =
              case term of
                P.Var      {}           -> l
                P.TyAbs    _x _tn k t   -> loop t $ (P.kindSize k, serialisedSize k) : l
                P.LamAbs   _x _n ty t   -> loop t $ (P.typeSize ty, serialisedSize ty) : l
                P.Apply    _x t1 t2     -> loop t2 $ loop t1 l
                P.Constant _x _c        -> l
                P.Builtin  _x _b        -> l
                P.TyInst   _x t ty      -> loop t $ (P.typeSize ty, serialisedSize ty) : l
                P.Unwrap   _x t         -> loop t l
                P.IWrap    _x ty1 ty2 t -> loop t $ (P.typeSize ty2, serialisedSize ty2)
                                                 : (P.typeSize ty1, serialisedSize ty1) : l
                P.Error    _x ty        -> (P.typeSize ty, serialisedSize ty) : l

analyseTypes :: P.Program P.TyName P.Name () -> IO ()
analyseTypes (P.Program _ _ body)= do
  let sizes = getTypeSizes body
  putStrLn "nodes bytes"
  mapM_ (putStrLn . \(a,b) -> show a ++ " " ++ show b) sizes

analyseProg :: String -> PlutusTx.CompiledCode a -> IO ()
analyseProg _name prg = do
--  putStrLn name
--  putStrLn ""
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
      q = deserialise s :: P.Program P.TyName P.Name ()
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

validatorHash2 :: Validator -> ValidatorHash
validatorHash2 vl = ValidatorHash $ BSL.fromStrict $ BA.convert h' where
    h :: Digest SHA256 = hash $ Write.toStrictByteString e
    h' :: Digest SHA256 = hash h
    e = encode vl

hashCode :: Validator -> Digest SHA256
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


{-# INLINABLE adder #-}
adder :: Integer
adder = 3 `B.addInteger` 5

testcode :: P.Program P.TyName P.Name ()
testcode =  PlutusTx.getPlc $ $$(PlutusTx.compile [|| adder ||])



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

vd1 :: P.Program P.TyName P.Name ()
vd1  =  PlutusTx.getPlc $ $$(PlutusTx.compile [|| factri  20 ||])

vd2 :: P.Program P.TyName P.Name ()
vd2  = PlutusTx.getPlc $ $$(PlutusTx.compile [|| factri  21 ||])
-- Can we compile the application, or apply the compiled version dynamically?


printResult :: Either E.CekMachineException P.EvaluationResultDef -> IO ()
printResult r =
    case r of
      Left _  -> putStrLn "Error"
      Right v -> putStrLn $ show v

--nodynamics :: M.DynamicBuiltinNameMeanings
--nodynamics = M.DynamicBuiltinNameMeanings Map.empty

type NodeIDs = Set.Set Integer

getUsedNodes :: (Either CekMarker.CekMachineException M.EvaluationResultDef, NodeIDs) -> NodeIDs
getUsedNodes (e, nodes) =
    case e of
     Left _                             -> error ()
     Right M.EvaluationFailure          -> error()
     Right (M.EvaluationSuccess _term ) -> nodes

compress :: B.ByteString -> B.ByteString
compress = G.compressWith G.defaultCompressParams {G.compressLevel = G.bestCompression}

unann :: Functor f => f a -> f()
unann x = () <$ x

merklisationAnalysis :: String -> PlutusTx.CompiledCode a -> IO ()
merklisationAnalysis _name code = do
  let program = PlutusTx.getPlc code
      s1 = serialise program
      numberedProgram = M.numberProgram program
      P.Program progAnn _ numberedBody = numberedProgram
      bodyAnn = P.termLoc numberedBody
      usedNodes =  getUsedNodes $ CekMarker.runCekWithStringBuiltins numberedProgram
      prunedProgram = M.pruneProgram usedNodes numberedProgram
      s2 = serialise prunedProgram
      hash1 = M.merkleHash $ M.fromCoreProgram program
      hash2 = M.merkleHash prunedProgram

--  T.putStrLn $ P.prettyPlcDefText numberedProgram
--  putStrLn $ show numberedProgram
--  T.putStrLn $ M.prettyPlcDefText prunedProgram
--  putStrLn $ show prunedProgram
  putStrLn "\nBefore Merklisation"
  putStrLn $ " AST size: " ++ (show $ PLCSize.astInfo program)
  putStrLn $ " Serialised size = " ++ (show $ BSL.length s1) ++ " bytes"
  putStrLn $ " Compressed size = " ++ (show $ BSL.length (compress s1)) ++ " bytes"
  putStrLn ""
  putStrLn "After Merklisation"
  putStrLn $ " Number of terms used during execution = " ++ (show $ Set.size usedNodes)  ---
--  putStrLn $ "Used nodes: " ++ (show usedNodes)
--  putStrLn $ "Prog ann = " ++ ( show progAnn)
--  putStrLn $ "Body ann = " ++ ( show bodyAnn)
  putStrLn $ " Remaining nodes: " ++ (show $ M.programSize prunedProgram)
  putStrLn $ " AST size: " ++ (show $ M.astInfo prunedProgram)
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
   histograms of the distribution of type sizes, and maybe the sizes of serialised types. -}


main :: IO ()
main = do
{-
  putStr "\n\n==========================\n\n"
  T.putStrLn $ P.prettyPlcDefText vd2
  putStr "\n\n==========================\n\n"
  T.putStrLn $ M.prettyPlcDefText prunedProgram
-}
    --  addressTest
--  dumpFlatTerm Future.exportedValidator
  let process = \_ prog -> analyseTypes $ PlutusTx.getPlc prog
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

-- Current validator is a little different for Future and PubKey

-- See plutus-use-cases/bench/Bench.hs for examples of manipulating PLC code
