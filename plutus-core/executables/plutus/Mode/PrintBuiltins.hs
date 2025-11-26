{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Mode.PrintBuiltins
  ( runPrintBuiltins
  ) where

import PlutusCore qualified as PLC
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Normalize (normalizeType)
import PlutusPrelude

import Data.List (intercalate)
import Data.Proxy (Proxy (..))
import GHC.TypeLits (symbolVal)
import Prettyprinter qualified as PP
import Text.Printf

runPrintBuiltins :: IO ()
runPrintBuiltins = portedImpl

-- following is PORTED from the older executable

portedImpl :: IO ()
portedImpl = do
  -- MAYBE: categorize the builtins by Plutus Version introduced. Would require dependency
  -- upon plutus-ledger-api
  let builtins = enumerate @PLC.DefaultFun
  mapM_
    (\x -> putStr (printf "%-35s: %s\n" (show $ PP.pretty x) (show $ getSignature x)))
    builtins
  where
    getSignature (PLC.toBuiltinMeaning @_ @_ @PlcTerm def -> PLC.BuiltinMeaning sch _ _) =
      typeSchemeToSignature sch

typeSchemeToSignature :: PLC.TypeScheme PlcTerm args res -> Signature
typeSchemeToSignature = toSig []
  where
    toSig :: [QVarOrType] -> PLC.TypeScheme PlcTerm args res -> Signature
    toSig acc =
      \case
        pR@PLC.TypeSchemeResult -> Signature acc (PLC.toTypeAst pR)
        arr@(PLC.TypeSchemeArrow schB) ->
          toSig (acc ++ [Type $ PLC.toTypeAst $ PLC.argProxy arr]) schB
        PLC.TypeSchemeAll proxy schK ->
          case proxy of
            (_ :: Proxy '(text, uniq, kind)) ->
              toSig (acc ++ [QVar $ symbolVal @text Proxy]) schK

type PlcTerm = PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun ()

-- Some types to represent signatures of built-in functions
type PlcType = PLC.Type PLC.TyName PLC.DefaultUni ()
data QVarOrType = QVar String | Type PlcType -- Quantified type variable or actual type
data Signature = Signature [QVarOrType] PlcType -- Argument types, return type

instance Show Signature where
  show (Signature args res) =
    "[ " ++ (intercalate ", " $ map showQT args) ++ " ] -> " ++ showTy (normTy res)
    where
      showQT =
        \case
          QVar tv -> "forall " ++ tv
          Type ty -> showTy (normTy ty)
      normTy :: PlcType -> PlcType
      normTy ty = PLC.runQuote $ PLC.unNormalized <$> normalizeType ty
      showTy ty =
        case ty of
          PLC.TyBuiltin _ t -> show $ PP.pretty t
          PLC.TyApp {} -> showMultiTyApp $ unwrapTyApp ty
          _ -> show $ PP.pretty ty
      unwrapTyApp ty =
        case ty of
          PLC.TyApp _ t1 t2 -> unwrapTyApp t1 ++ [t2]
          -- Assumes iterated built-in type applications all associate to the left;
          -- if not, we'll just get some odd formatting.
          _ -> [ty]
      showMultiTyApp =
        \case
          [] -> "<empty type application>" -- Should never happen
          op : tys -> showTy op ++ "(" ++ intercalate ", " (map showTy tys) ++ ")"
