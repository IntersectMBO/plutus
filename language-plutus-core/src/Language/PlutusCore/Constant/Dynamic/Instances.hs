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
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Sum         as Plc
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Meta.Data.Tuple
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type

import           Control.Monad.Except
import           Data.Bitraversable
import           Data.Char
import           Data.Proxy
import qualified Data.Text.Prettyprint.Doc                   as Doc
import           System.IO.Unsafe                            (unsafePerformIO)

instance KnownDynamicBuiltinType a => KnownDynamicBuiltinType (EvaluationResult a) where
    toTypeEncoding _ = toTypeEncoding @a Proxy

    -- 'EvaluationFailure' on the Haskell side becomes 'Error' on the PLC side.
    makeDynamicBuiltin EvaluationFailure     = pure . Error () $ toTypeEncoding @a Proxy
    makeDynamicBuiltin (EvaluationSuccess x) = makeDynamicBuiltin x

    -- There are two 'EvaluationResult's here: an external one (which any 'KnownType'
    -- instance has to deal with) and an internal one (specific to this particular instance).
    -- Our approach is to always return 'EvaluationSuccess' for the external 'EvaluationResult'
    -- and catch all 'EvaluationFailure's in the internal 'EvaluationResult'.
    -- This allows *not* to short-circuit when 'readKnown' fails to read a Haskell value.
    -- Instead the user gets an explicit @EvaluationResult a@ and evaluation proceeds normally.
    readDynamicBuiltin eval term = makeReflectT $ EvaluationSuccess <$> do
        res <- eval mempty term
        fmap (fmap join . sequence) . runReflectT $ traverse (readDynamicBuiltin eval) res

instance KnownDynamicBuiltinType [Char] where
    toTypeEncoding _ = TyBuiltin () TyString

    makeDynamicBuiltin = pure . Constant () . makeBuiltinStr

    readDynamicBuiltin eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinStr () s) -> pure s
            _                             -> throwError "Not a builtin String"

instance KnownDynamicBuiltinType Bool where
    toTypeEncoding _ = bool

    makeDynamicBuiltin b = Just $ if b then true else false

    readDynamicBuiltin eval b = do
        let int1 = TyApp () (TyBuiltin () TyInteger) (TyInt () 4)
            asInt1 = Constant () . BuiltinInt () 1
            -- Encode 'Bool' from Haskell as @integer 1@ from PLC.
            term = mkIterApp () (TyInst () b int1) [asInt1 1, asInt1 0]
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinInt () 1 1) -> pure True
            Constant () (BuiltinInt () 1 0) -> pure False
            _                               -> throwError "Not an integer-encoded Bool"

-- Encode 'Char' from Haskell as @integer 4@ from PLC.
instance KnownDynamicBuiltinType Char where
    toTypeEncoding _ = TyApp () (TyBuiltin () TyInteger) (TyInt () 4)

    makeDynamicBuiltin = fmap (Constant ()) . makeBuiltinInt 4 . fromIntegral . ord

    readDynamicBuiltin eval term = do
        -- 'term' is supposed to be already evaluated, but calling 'eval' is the easiest way
        -- to turn 'Error' into 'EvaluationFailure', which we later 'lift' to 'Convert'.
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant () (BuiltinInt () 4 int) -> pure . chr $ fromIntegral int
            _                                 -> throwError "Not an integer-encoded Char"

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
            (xs, (ys, getRes)) =
                unsafePerformIO . withEmitHandler eval $
                    withEmitTerm TypedBuiltinDyn $ \emitX ->
                    withEmitTerm TypedBuiltinDyn $ \emitY ->
                        feedEmitHandler $ go emitX emitY
        _ <- makeRightReflectT getRes
        case (xs, ys) of
            ([x], [y]) -> pure (x, y)
            _          -> throwError "Not a (,)"

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
        _ <- makeRightReflectT getRes
        case (l, r) of
            ([x], []) -> pure $ Left  x
            ([], [y]) -> pure $ Right y
            _         -> throwError "Not an Either"

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
        _ <- makeRightReflectT getRes
        pure $ PlcList xs

instance PrettyDynamic a => PrettyDynamic (PlcList a) where
    prettyDynamic = Doc.list . map prettyDynamic . unPlcList
