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
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Sum         as Plc
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Meta.Data.Tuple
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type

import           Data.Bitraversable
import           Data.Char
import           Data.Proxy
import qualified Data.Text.Prettyprint.Doc                   as Doc
import           System.IO.Unsafe                            (unsafePerformIO)

instance KnownDynamicBuiltinType [Char] where
    toTypeEncoding _ = TyBuiltin () TyString

    makeDynamicBuiltin = Just . Constant () . makeBuiltinStr

    readDynamicBuiltin _ (Constant () (BuiltinStr () s)) = pure $ Just s
    readDynamicBuiltin _ _                               = pure Nothing

-- Encode 'Char' from Haskell as @integer 4@ from PLC.
instance KnownDynamicBuiltinType Char where
    toTypeEncoding _ = TyApp () (TyBuiltin () TyInteger) (TyInt () 4)

    makeDynamicBuiltin = fmap (Constant ()) . makeBuiltinInt 4 . fromIntegral . ord

    readDynamicBuiltin _ (Constant () (BuiltinInt () 4 int)) = pure . Just . chr $ fromIntegral int
    readDynamicBuiltin _ _                                   = pure Nothing

instance PrettyDynamic Char

proxyOf :: a -> Proxy a
proxyOf _ = Proxy

makeTypeAndDynamicBuiltin
    :: KnownDynamicBuiltinType a => a -> Maybe (Type TyName (), Term TyName Name ())
makeTypeAndDynamicBuiltin x = do
    let da = toTypeEncoding $ proxyOf x
    dx <- makeDynamicBuiltin x
    pure (da, dx)

instance (KnownDynamicBuiltinType a, KnownDynamicBuiltinType b) =>
            KnownDynamicBuiltinType (a, b) where
    toTypeEncoding _ =
        mkIterTyApp () (prodN 2)
            [ toTypeEncoding $ Proxy @a
            , toTypeEncoding $ Proxy @b
            ]

    makeDynamicBuiltin (x, y) = do
        dax <- makeTypeAndDynamicBuiltin x
        dby <- makeTypeAndDynamicBuiltin y
        pure . _tupleTerm . runQuote $ getSpineToTuple () [dax, dby]

    readDynamicBuiltin eval dxy = do
        let go emitX emitY = runQuote $ do
                let da = toTypeEncoding $ Proxy @a
                    db = toTypeEncoding $ Proxy @b
                dx <- freshName () "x"
                dy <- freshName () "y"
                pure
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
        pure $ case (xs, ys) of
            ([x], [y]) -> (x, y) <$ evaluationResultToMaybe res
            _          -> Nothing  -- TODO: use descriptive error messages?

instance (KnownDynamicBuiltinType a, KnownDynamicBuiltinType b) =>
            KnownDynamicBuiltinType (Either a b) where
    toTypeEncoding _ =
        mkIterTyApp () Plc.sum
            [ toTypeEncoding $ Proxy @a
            , toTypeEncoding $ Proxy @b
            ]

    makeDynamicBuiltin s = do
        let da = toTypeEncoding $ Proxy @a
            db = toTypeEncoding $ Proxy @b
        ds <- bitraverse makeDynamicBuiltin makeDynamicBuiltin s
        pure $ metaEitherToSum da db ds

    readDynamicBuiltin eval ds = do
        let go emitX emitY = mkIterApp () (TyInst () ds unit) [emitX, emitY]
            (l, (r, getRes)) =
                unsafePerformIO . withEmitHandler eval $
                    withEmitTerm TypedBuiltinDyn $ \emitX ->
                    withEmitTerm TypedBuiltinDyn $ \emitY ->
                        feedEmitHandler $ go emitX emitY
        res <- getRes
        pure $ case (l, r) of
            ([x], []) -> Left  x <$ evaluationResultToMaybe res
            ([], [y]) -> Right y <$ evaluationResultToMaybe res
            _         -> Nothing

newtype PlcList a = PlcList
    { unPlcList :: [a]
    } deriving (Eq, Show)

instance KnownDynamicBuiltinType a => KnownDynamicBuiltinType (PlcList a) where
    toTypeEncoding _ = TyApp () (_recursiveType listData) $ toTypeEncoding (Proxy @a)

    makeDynamicBuiltin (PlcList xs) = do
        dyns <- traverse makeDynamicBuiltin xs
        let argTy = toTypeEncoding $ Proxy @a
        pure $ metaListToList argTy dyns

    readDynamicBuiltin eval list = do
        let go emit = runQuote $ do
                -- foldList {a} {unit} (\(r : unit) -> emit) unitval list
                let a = toTypeEncoding $ Proxy @a
                u <- freshName () "u"
                pure $
                    mkIterApp () (mkIterInst () foldList [a, unit])
                        [LamAbs () u unit emit, unitval, list]
            (xs, getRes) = unsafePerformIO $ withEmitEvaluateBy eval TypedBuiltinDyn go
        res <- getRes
        pure $ PlcList xs <$ evaluationResultToMaybe res

instance PrettyDynamic a => PrettyDynamic (PlcList a) where
    prettyDynamic = Doc.list . map prettyDynamic . unPlcList
