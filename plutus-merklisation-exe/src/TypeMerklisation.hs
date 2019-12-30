{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module TypeMerklisation where

import qualified Codec.Compression.GZip                                        as G
import           Codec.Serialise                                               (serialise)
import           Crypto.Hash
import qualified Data.ByteArray                                                as BA
import qualified Data.ByteString.Lazy                                          as B
import           Data.Functor.Foldable
import qualified Data.Text                                                     as D
import           Data.Text.Encoding                                            (encodeUtf8)
import           GHC.Int                                                       (Int64)
import           GHC.Natural                                                   (Natural)
import           Numeric

import qualified Language.PlutusCore                                           as P
import qualified Language.PlutusCore.Merkle.CBOR                               as M
import           Language.PlutusCore.Merkle.Merklisable                        (Merklisable, merkleHash)
import qualified Language.PlutusCore.Merkle.PLCSize                            as PLCSize
import qualified Language.PlutusCore.Merkle.Size                               as M
import qualified Language.PlutusCore.Merkle.Size                               as M
import qualified Language.PlutusCore.Merkle.Type                               as M


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

import qualified Language.PlutusTx                                             as PlutusTx

--- Merklise types away

translateKind :: P.Kind ann -> M.Kind ann
translateKind = \case
         P.Type x            -> M.Type x
         P.KindArrow x k1 k2 -> M.KindArrow x (translateKind k1) (translateKind k2)

translateBuiltin :: P.Builtin ann -> M.Builtin ann
translateBuiltin = \case
  P.BuiltinName x n    -> M.BuiltinName x n
  P.DynBuiltinName x n -> M.DynBuiltinName x n

translateConstant :: P.Constant ann -> M.Constant ann
translateConstant = \case
     P.BuiltinInt x n -> M.BuiltinInt x n
     P.BuiltinBS x s  -> M.BuiltinBS x s
     P.BuiltinStr x s -> M.BuiltinStr x s



merkliseType :: Merklisable ann => P.Type P.TyName ann -> M.Type P.TyName ann
merkliseType ty = M.TyPruned (P.tyLoc ty) (merkleHash ty)

merkliseTypes :: Merklisable ann => P.Term P.TyName P.Name ann -> M.Term P.TyName P.Name ann
merkliseTypes = \case
      P.Var      x n         -> M.Var      x n
      P.TyAbs    x tn k t    -> M.TyAbs    x tn (translateKind k) (merkliseTypes t)
      P.LamAbs   x n ty t    -> M.LamAbs   x n (merkliseType ty) (merkliseTypes t)
      P.Apply    x t1 t2     -> M.Apply    x (merkliseTypes t1) (merkliseTypes t2)
      P.Constant x c         -> M.Constant x (translateConstant c)
      P.Builtin  x b         -> M.Builtin  x (translateBuiltin b)
      P.TyInst   x t ty      -> M.TyInst   x (merkliseTypes t) (merkliseType ty)
      P.Unwrap   x t         -> M.Unwrap   x (merkliseTypes t)
      P.IWrap    x ty1 ty2 t -> M.IWrap    x (merkliseType ty1) (merkliseType ty2) (merkliseTypes t)
      P.Error    x ty        -> M.Error    x (merkliseType ty)

merkliseProgramTypes :: Merklisable ann => P.Program P.TyName P.Name ann -> M.Program P.TyName P.Name ann
merkliseProgramTypes (P.Program x version body) = M.Program x version (merkliseTypes body)


{- Problem: Digests have type ByteArrayAccess, so we can hash them (again).
   We'd like to concatenate Digests then hash them, so we can generate a digest
   involving the children of a node.  Now we wave

       class (Eq ba, Ord ba, Monoid ba, ByteArrayAccess ba) => ByteArray ba

   and ByteArray does have concatenation.  Digest has Eq and Ord, but not Monoid.

   We'd need an mempty for Digest, which seems improbable.
-}

data CompressionMode = Uncompressed | Compressed
data PrintFormat = Alone | WithPercentage

compress :: B.ByteString -> B.ByteString
compress s = G.compressWith G.defaultCompressParams {G.compressLevel = G.bestCompression} s

printHeader :: IO ()
printHeader = do
  putStrLn "| Contract | Total Nodes | Type nodes | Serialised Size | Serialised, types Merklised |"
  putStrLn "| :---: | ---: | ---: | ---: | ---: |"

printSeparator :: IO ()
printSeparator = pure ()
printEntry :: Int64 -> B.ByteString -> PrintFormat -> CompressionMode -> IO ()
printEntry fullSize s mode cmode = do
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


analyseProg :: String -> PlutusTx.CompiledCode a -> IO()
analyseProg name code = do
    let prog = PlutusTx.getPlc code
        numNodes = PLCSize.programSize prog
        numTypeNodes = PLCSize.programNumTypeNodes prog
        s1 = serialise prog
        s2 = serialise $ merkliseProgramTypes prog
        fullSize = B.length s1
    putStr $ "| " ++ name ++ " | "
    putStr $ show numNodes
    putStr " | "
    putStr $ show numTypeNodes
    putStr " | "
    printEntry fullSize s1 WithPercentage Uncompressed
    putStr " | "
    printEntry fullSize s2 WithPercentage Uncompressed
    putStrLn " | "
    putStr "| (Compressed) | | | "
    printEntry fullSize s1 WithPercentage Compressed
    putStr " | "
    printEntry fullSize s2 WithPercentage Compressed
    putStrLn " |"


analyseContracts :: IO ()
analyseContracts = do
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

-- Looking at duplicated types

getTypesTerm :: P.Term P.TyName P.Name () -> ([P.Type P.TyName ()], [P.Kind ()])
getTypesTerm = cata a where
    a P.VarF{}              = mempty
    a (P.TyAbsF _ _ k t)    = t <> ([], [k])
    a (P.ApplyF _ t t')     = t <> t'
    a (P.LamAbsF _ _ ty t)  = ([ty],[]) <> t
    a P.ConstantF{}         = mempty
    a P.BuiltinF{}          = mempty
    a (P.TyInstF _ t ty)    = ([ty],[]) <> t
    a (P.UnwrapF _ t)       = t
    a (P.IWrapF _ ty ty' t) = ([ty,ty'],[]) <> t
    a (P.ErrorF _ ty)       = ([ty],[])

getTypes :: PlutusTx.CompiledCode a -> ([P.Type P.TyName ()], [P.Kind ()])
getTypes code =
    let P.Program _ _ body = () <$ PlutusTx.getPlc code
    in getTypesTerm body

printTypes ::  String -> PlutusTx.CompiledCode a -> IO ()
printTypes name code = do
  let (types, kinds) = getTypes code
      showType t = (show $ PLCSize.typeSize t) ++ ": " ++ (show t)
      showKind k = (show $ PLCSize.kindSize k) ++ ": " ++ (show k)
  mapM_ (putStrLn . showKind) kinds


main :: IO ()
main = printTypes "MultiSigStateMachine" MultiSigStateMachine.exportedValidator
