-- | A dynamic built-in type test.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.Builtin.Instances
    () where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Type

import           Language.PlutusCore.Builtin.Common

import           Data.Char
import           Data.Functor                          (void)
import           Data.Functor.Compose                  (Compose (..))
import           Data.Proxy
import           System.IO.Unsafe                      (unsafePerformIO)

argumentProxy :: proxy (f a) -> Proxy a
argumentProxy _ = Proxy

withResultProxy :: (Proxy dyn -> result dyn) -> result dyn
withResultProxy k = k Proxy

-- Encode 'Char' from Haskell as @integer 4@ from PLC.
instance KnownDynamicBuiltinType Char where
    getTypeEncoding _ = return $ TyApp () (TyBuiltin () TyInteger) (TyInt () 4)

    makeDynamicBuiltin = pure . fmap (Constant ()) . makeBuiltinInt 4 . fromIntegral . ord

    readDynamicBuiltin (Constant () (BuiltinInt () 4 int)) = Just . chr $ fromIntegral int
    readDynamicBuiltin _                                   = Nothing

instance PrettyDynamic Char

instance KnownDynamicBuiltinType dyn => KnownDynamicBuiltinType [dyn] where
    getTypeEncoding proxyListDyn =
        fmap (_recursiveType . holedToRecursive) $
            holedTyApp <$> getBuiltinList <*> getTypeEncoding (argumentProxy proxyListDyn)

    makeDynamicBuiltin xs = do
        mayDyns <- getCompose $ traverse (Compose . makeDynamicBuiltin) xs
        argTy <- getTypeEncoding xs  -- Here we use '[]' as a @proxy@. Don't judge me, I'm only human.
        traverse (getListToBuiltinList argTy) mayDyns

    readDynamicBuiltin list = withResultProxy $ \proxyListDyn -> do
        let (xs, errOrRes) =
                unsafePerformIO . withEmitTypecheckEvaluate TypedBuiltinDyn $ \emit ->
                    -- foldList {dyn} {()} (\(r : unit) -> emit) unitval list
                    runQuote $ do
                        dyn      <- getTypeEncoding $ argumentProxy proxyListDyn
                        unit     <- getBuiltinUnit
                        unitval  <- getBuiltinUnitval
                        foldList <- getBuiltinFoldList
                        u <- freshName () "u"
                        return
                            $ mkIterApp () (mkIterInst () foldList [dyn, unit])
                                [LamAbs () u unit emit, unitval, list]
        case errOrRes of
            Left err  -> error $ prettyPlcDefString err
            Right res -> void $ evaluationResultToMaybe res
        Just xs

blah :: Maybe String
blah = runQuote (makeDynamicBuiltin ("abc" :: String)) >>= readDynamicBuiltin

instance PrettyDynamic a => PrettyDynamic [a] where
    prettyDynamic = undefined
