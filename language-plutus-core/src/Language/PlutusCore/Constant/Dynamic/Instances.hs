{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Constant.Dynamic.Instances
    () where

import           Language.PlutusCore.Constant.Dynamic.Emit
import           Language.PlutusCore.Constant.Dynamic.Pretty
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type

import           Data.Char
import           Data.Functor.Compose                        (Compose (..))
import           Data.Proxy
import qualified Data.Text.Prettyprint.Doc                   as Doc
import           System.IO.Unsafe                            (unsafePerformIO)

argumentProxy :: proxy (f a) -> Proxy a
argumentProxy _ = Proxy

withResultProxy :: (Proxy dyn -> result dyn) -> result dyn
withResultProxy k = k Proxy

-- Encode 'Char' from Haskell as @integer 4@ from PLC.
instance KnownDynamicBuiltinType Char where
    getTypeEncoding _ = return $ TyApp () (TyBuiltin () TyInteger) (TyInt () 4)

    makeDynamicBuiltin = pure . fmap (Constant ()) . makeBuiltinInt 4 . fromIntegral . ord

    readDynamicBuiltin _ (Constant () (BuiltinInt () 4 int)) = Just . chr $ fromIntegral int
    readDynamicBuiltin _ _                                   = Nothing

instance PrettyDynamic Char

instance KnownDynamicBuiltinType dyn => KnownDynamicBuiltinType [dyn] where
    getTypeEncoding proxyListDyn =
        fmap (_recursiveType . holedToRecursive) $
            holedTyApp <$> getBuiltinList <*> getTypeEncoding (argumentProxy proxyListDyn)

    makeDynamicBuiltin xs = do
        mayDyns <- getCompose $ traverse (Compose . makeDynamicBuiltin) xs
        argTy <- getTypeEncoding xs  -- Here we use '[]' as a @proxy@. Don't judge me, I'm only human.
        traverse (getListToBuiltinList argTy) mayDyns

    readDynamicBuiltin eval list = withResultProxy $ \proxyListDyn -> do
        let go emit = runQuote $ do
                -- foldList {dyn} {unit} (\(r : unit) -> emit) unitval list
                dyn      <- getTypeEncoding $ argumentProxy proxyListDyn
                unit     <- getBuiltinUnit
                unitval  <- getBuiltinUnitval
                foldList <- getBuiltinFoldList
                u <- freshName () "u"
                return $
                    mkIterApp () (mkIterInst () foldList [dyn, unit])
                        [LamAbs () u unit emit, unitval, list]
            (xs, res) = unsafePerformIO $ withEmitEvaluateBy eval TypedBuiltinDyn go
        _ <- evaluationResultToMaybe res
        Just xs

instance PrettyDynamic a => PrettyDynamic [a] where
    prettyDynamic = Doc.list . map prettyDynamic
