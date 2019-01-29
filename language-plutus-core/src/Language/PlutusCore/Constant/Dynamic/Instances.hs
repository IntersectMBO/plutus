{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Language.PlutusCore.Constant.Dynamic.Instances
    ( PlcList (..)
    ) where

import           Language.PlutusCore.Constant.Dynamic.Emit
import           Language.PlutusCore.Constant.Dynamic.Pretty
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.List        hiding (getBuiltinSum)
import           Language.PlutusCore.StdLib.Data.Sum
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Meta.Data.Tuple
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type

import           Control.Monad.Trans.Maybe
import           Data.Bitraversable
import           Data.Char
import           Data.Functor.Compose                        (Compose (..))
import           Data.Proxy
import qualified Data.Text.Prettyprint.Doc                   as Doc
import           System.IO.Unsafe                            (unsafePerformIO)

instance KnownDynamicBuiltinType [Char] where
    getTypeEncoding _ = return $ TyBuiltin () TyString

    makeDynamicBuiltin = return . Just . Constant () . makeBuiltinStr

    readDynamicBuiltin _ (Constant () (BuiltinStr () s)) = return $ Just s
    readDynamicBuiltin _ _                               = return Nothing

-- Encode 'Char' from Haskell as @integer 4@ from PLC.
instance KnownDynamicBuiltinType Char where
    getTypeEncoding _ = return $ TyApp () (TyBuiltin () TyInteger) (TyInt () 4)

    makeDynamicBuiltin = pure . fmap (Constant ()) . makeBuiltinInt 4 . fromIntegral . ord

    readDynamicBuiltin _ (Constant () (BuiltinInt () 4 int)) = return . Just . chr $ fromIntegral int
    readDynamicBuiltin _ _                                   = return Nothing

instance PrettyDynamic Char

proxyOf :: a -> Proxy a
proxyOf _ = Proxy

makeTypeAndDynamicBuiltin
    :: KnownDynamicBuiltinType a => a -> MaybeT Quote (Type TyName (), Term TyName Name ())
makeTypeAndDynamicBuiltin x = do
    da <- liftQuote $ getTypeEncoding $ proxyOf x
    dx <- MaybeT $ makeDynamicBuiltin x
    pure (da, dx)

instance (KnownDynamicBuiltinType a, KnownDynamicBuiltinType b) =>
            KnownDynamicBuiltinType (a, b) where
    getTypeEncoding _ =
        mkIterTyApp () <$> getBuiltinProdN 2 <*> sequence
            [ getTypeEncoding $ Proxy @a
            , getTypeEncoding $ Proxy @b
            ]

    makeDynamicBuiltin (x, y) = runMaybeT $ do
        dax <- makeTypeAndDynamicBuiltin x
        dby <- makeTypeAndDynamicBuiltin y
        liftQuote $ _tupleTerm <$> getSpineToTuple () [dax, dby]

    readDynamicBuiltin eval dxy = do
        let go emitX emitY = runQuote $ do
                unit <- getBuiltinUnit
                sequ <- getBuiltinSequ
                da <- getTypeEncoding $ Proxy @a
                db <- getTypeEncoding $ Proxy @b
                dx <- freshName () "x"
                dy <- freshName () "y"
                return
                    . Apply () (TyInst () dxy unit)
                    . LamAbs () dx da
                    . LamAbs () dy db
                    $ mkIterApp () sequ
                        [ Apply () emitX $ Var () dx
                        , Apply () emitY $ Var () dy
                        ]
        let (xs, (ys, getRes)) =
                unsafePerformIO . withEmitHandler eval $
                    withEmitTerm TypedBuiltinDyn $ \emitX ->
                    withEmitTerm TypedBuiltinDyn $ \emitY ->
                        feedEmitHandler $ go emitX emitY
        res <- getRes
        case (xs, ys) of
            ([x], [y]) -> return $ (x, y) <$ evaluationResultToMaybe res
            _          -> return Nothing  -- TODO: use descriptive error messages?

instance (KnownDynamicBuiltinType a, KnownDynamicBuiltinType b) =>
            KnownDynamicBuiltinType (Either a b) where
    getTypeEncoding _ =
        mkIterTyApp () <$> getBuiltinSum <*> sequence
            [ getTypeEncoding $ Proxy @a
            , getTypeEncoding $ Proxy @b
            ]

    makeDynamicBuiltin s = do
        da <- getTypeEncoding $ Proxy @a
        db <- getTypeEncoding $ Proxy @b
        runMaybeT $ do
            -- TODO: definitely should have 'MaybeT' by default.
            ds <- bitraverse (MaybeT . makeDynamicBuiltin) (MaybeT . makeDynamicBuiltin) s
            liftQuote $ getEitherToBuiltinSum da db ds

    readDynamicBuiltin eval ds = do
        let go emitX emitY = runQuote $ do
                unit <- getBuiltinUnit
                return $ mkIterApp () (TyInst () ds unit) [emitX, emitY]
        let (l, (r, getRes)) =
                unsafePerformIO . withEmitHandler eval $
                    withEmitTerm TypedBuiltinDyn $ \emitX ->
                    withEmitTerm TypedBuiltinDyn $ \emitY ->
                        feedEmitHandler $ go emitX emitY
        res <- getRes
        case (l, r) of
            ([x], []) -> return $ Left  x <$ evaluationResultToMaybe res
            ([], [y]) -> return $ Right y <$ evaluationResultToMaybe res
            _         -> return Nothing

newtype PlcList a = PlcList
    { unPlcList :: [a]
    } deriving (Eq, Show)

instance KnownDynamicBuiltinType a => KnownDynamicBuiltinType (PlcList a) where
    getTypeEncoding _ =
        TyApp ()
            <$> fmap _recursiveType getBuiltinList
            <*> getTypeEncoding (Proxy @a)

    makeDynamicBuiltin (PlcList xs) = do
        mayDyns <- getCompose $ traverse (Compose . makeDynamicBuiltin) xs
        argTy <- getTypeEncoding $ Proxy @a
        traverse (getListToBuiltinList argTy) mayDyns

    readDynamicBuiltin eval list = do
        let go emit = runQuote $ do
                -- foldList {a} {unit} (\(r : unit) -> emit) unitval list
                a        <- getTypeEncoding $ Proxy @a
                unit     <- getBuiltinUnit
                unitval  <- getBuiltinUnitval
                foldList <- getBuiltinFoldList
                u <- freshName () "u"
                return $
                    mkIterApp () (mkIterInst () foldList [a, unit])
                        [LamAbs () u unit emit, unitval, list]
            (xs, getRes) = unsafePerformIO $ withEmitEvaluateBy eval TypedBuiltinDyn go
        res <- getRes
        return $ PlcList xs <$ evaluationResultToMaybe res

instance PrettyDynamic a => PrettyDynamic (PlcList a) where
    prettyDynamic = Doc.list . map prettyDynamic . unPlcList
