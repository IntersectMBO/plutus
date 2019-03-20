{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
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
import           Data.Functor
import           Data.Proxy
import qualified Data.Text.Prettyprint.Doc                   as Doc
import           System.IO.Unsafe                            (unsafePerformIO)

instance KnownDynamicBuiltinType a => KnownDynamicBuiltinType (EvaluationResult a) where
    toTypeEncoding _ = toTypeEncoding @a Proxy

    -- 'EvaluationFailure' on the Haskell side becomes 'Error' on the PLC side.
    makeDynamicBuiltin EvaluationFailure     = pure . Error () $ toTypeEncoding @a Proxy
    makeDynamicBuiltin (EvaluationSuccess x) = makeDynamicBuiltin x

    -- There are two 'EvaluationResult's here: an external one (which any 'KnownDynamicBuiltinType'
    -- instance has to deal with) and an internal one (specific to this particular instance).
    -- Our approach is to always return 'EvaluationSuccess' for the external 'EvaluationResult'
    -- and catch all 'EvaluationFailure's in the internal 'EvaluationResult'.
    -- This allows *not* to short-circuit when 'readDynamicBuiltin' fails to read a Haskell value.
    -- Instead the user gets an explicit @EvaluationResult a@ and evaluation proceeds normally.
    readDynamicBuiltin eval term = ExceptT . EvaluationSuccess <$> do
        res <- eval mempty term
        sequence . (>>= runExceptT) <$> traverse (readDynamicBuiltin eval) res

instance KnownDynamicBuiltinType [Char] where
    toTypeEncoding _ = TyBuiltin () TyString

    makeDynamicBuiltin = pure . Constant () . makeBuiltinStr

    readDynamicBuiltin eval term = do
        res <- eval mempty term
        pure $ lift res >>= \case
            Constant () (BuiltinStr () s) -> pure s
            _                             -> throwError "Not a builtin String"

instance KnownDynamicBuiltinType Bool where
    toTypeEncoding _ = bool

    makeDynamicBuiltin b = pure $ if b then true else false

    readDynamicBuiltin eval b = do
        let int1 = TyApp () (TyBuiltin () TyInteger) (TyInt () 4)
            asInt1 = Constant () . BuiltinInt () 1
        -- Encode 'Bool' from Haskell as @integer 1@ from PLC.
        res <- eval mempty (mkIterApp () (TyInst () b int1) [asInt1 1, asInt1 0])
        pure $ lift res >>= \case
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
        res <- eval mempty term
        pure $ lift res >>= \case
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
            [ toTypeEncoding @a Proxy
            , toTypeEncoding @b Proxy
            ]

    makeDynamicBuiltin (x, y) = do
        dax <- makeTypeAndDynamicBuiltin x
        dby <- makeTypeAndDynamicBuiltin y
        pure . _tupleTerm . runQuote $ getSpineToTuple () [dax, dby]

    readDynamicBuiltin eval dxy = do
        let go emitX emitY = runQuote $ do
                let da = toTypeEncoding @a Proxy
                    db = toTypeEncoding @b Proxy
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
            ([x], [y]) -> (x, y) <$ lift res
            _          -> throwError "Not a (,)"

instance (KnownDynamicBuiltinType a, KnownDynamicBuiltinType b) =>
            KnownDynamicBuiltinType (Either a b) where
    toTypeEncoding _ =
        mkIterTyApp () Plc.sum
            [ toTypeEncoding @a Proxy
            , toTypeEncoding @b Proxy
            ]

    makeDynamicBuiltin s = do
        let da = toTypeEncoding @a Proxy
            db = toTypeEncoding @b Proxy
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
            ([x], []) -> Left  x <$ lift res
            ([], [y]) -> Right y <$ lift res
            _         -> throwError "Not an Either"

newtype PlcList a = PlcList
    { unPlcList :: [a]
    } deriving (Eq, Show)

instance KnownDynamicBuiltinType a => KnownDynamicBuiltinType (PlcList a) where
    toTypeEncoding _ = TyApp () (_recursiveType listData) $ toTypeEncoding (Proxy @a)

    makeDynamicBuiltin (PlcList xs) = do
        dyns <- traverse makeDynamicBuiltin xs
        let argTy = toTypeEncoding @a Proxy
        pure $ metaListToList argTy dyns

    -- A natural implementation of this function would be to emit elements of a list one by one
    -- until evaluation of a Plutus Core term finishes. However this approach doesn't scale to other
    -- recursive types, because linear streaming is not suitable for handling tree-like structures.
    -- Another option would be to collect a Haskell value inside a Plutus Core accumulator while
    -- evaluating things on the Plutus Core side. However embedding the entire Haskell into
    -- Plutus Core is a little bit weird and we would need runtime type equality checks
    -- (the simplest way would probably be to use @Dynamic@) or some other trickery.
    -- Here instead we do something very simple: we pattern match in Plutus Core on a list, return
    -- the pieces we got from the pattern match and then recreate the list on the Haskell side.
    -- And that's all.
    -- How a single pattern match can handle a recursive data structure? All of the pieces that we
    -- get from the pattern matching get converted to Haskell and one of those pieces is the tail
    -- of the list. That is, we implicitly invoke 'readDynamicBuiltin' recursively until the list
    -- is empty.
    readDynamicBuiltin eval list = do
        let term = runQuote $ do
                -- > unwrap list {sum unit (prodN 2 a (list a))} unitval
                -- >     \(x : a) (xs : list a) -> prodNConstructor 2 {a} {list a} x xs
                let listA = toTypeEncoding @(PlcList a) Proxy
                    a     = toTypeEncoding @a           Proxy
                    resL = unit
                    resR = mkIterTyApp () (prodN 2) [a, listA]
                    -- TODO: use 'maybe' instead of 'sum'.
                    res  = mkIterTyApp () Plc.sum [resL, resR]
                x  <- freshName () "x"
                xs <- freshName () "xs"
                pure $ mkIterApp () (TyInst () (Unwrap () list) res)
                    [ Apply () (mkIterInst () Plc.left [resL, resR]) unitval
                    ,   LamAbs () x  a
                      . LamAbs () xs listA
                      . Apply () (mkIterInst () Plc.right [resL, resR])
                      $ mkIterApp () (mkIterInst () (prodNConstructor 2) [a, listA])
                          [ Var () x, Var () xs ]
                    ]
        readDynamicBuiltin eval term <&> \conv -> conv <&> \res ->
            PlcList $ case res of
                Left  ()              -> []
                Right (x, PlcList xs) -> x : xs

instance PrettyDynamic a => PrettyDynamic (PlcList a) where
    prettyDynamic = Doc.list . map prettyDynamic . unPlcList
