{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Plutus.CoreToPLC.Utils where

import qualified Language.PlutusCore  as PLC

import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text            as T
import qualified Data.Text.Encoding   as TE

import           GHC.Natural

strToBs :: String -> BSL.ByteString
strToBs = BSL.fromStrict . TE.encodeUtf8 . T.pack

bsToStr :: BSL.ByteString -> String
bsToStr = T.unpack . TE.decodeUtf8 . BSL.toStrict

instSize :: Natural -> PLC.Term tyname name () -> PLC.Term tyname name ()
instSize n t = PLC.TyInst () t (PLC.TyInt () n)

appSize :: Natural -> PLC.Type tyname () -> PLC.Type tyname ()
appSize n t = PLC.TyApp () t (PLC.TyInt () n)

mkConstant :: PLC.BuiltinName -> PLC.Term tyname name ()
mkConstant n = PLC.Constant () $ PLC.BuiltinName () n

mkIntFun :: PLC.BuiltinName -> PLC.Term PLC.TyName PLC.Name ()
mkIntFun name = instSize haskellIntSize (mkConstant name)

mkIntRel :: PLC.BuiltinName -> PLC.Term PLC.TyName PLC.Name ()
mkIntRel name = instSize haskellIntSize (mkConstant name)

mkBsRel :: PLC.BuiltinName -> PLC.Term PLC.TyName PLC.Name ()
mkBsRel name = instSize haskellBSSize (mkConstant name)

haskellIntSize :: Natural
haskellIntSize = 64

haskellBSSize :: Natural
haskellBSSize = 64
