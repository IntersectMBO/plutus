-- | Instances of the 'KnownType' class.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Language.PlutusCore.Merkle.Constant.Dynamic.Instances
    ( PlcList (..)
    ) where

import           Language.PlutusCore.Lexer.Type               (prettyBytes)
import           Language.PlutusCore.Merkle.Constant.Make
import           Language.PlutusCore.Merkle.Constant.Typed
import           Language.PlutusCore.Merkle.Evaluation.Result
import           Language.PlutusCore.MkPlc
-- ^ NOT Merkle.MkPlc.  The stuff here is only supposed to deal with standard Terms/Types, not the Merkle versions.
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Data.Bool
import qualified Language.PlutusCore.StdLib.Data.Function     as Plc
import           Language.PlutusCore.StdLib.Data.Sum          as Plc
import           Language.PlutusCore.StdLib.Data.Unit
import           Language.PlutusCore.StdLib.Meta.Data.Tuple
import           Language.PlutusCore.StdLib.Type
import           Language.PlutusCore.Type

import           Control.Monad.Except
import           Data.Bifunctor
import qualified Data.ByteString.Lazy                         as BSL
import           Data.Char
import           Data.Proxy
import qualified Data.Set
import qualified Data.Text                                    as Text
import qualified Data.Text.Prettyprint.Doc                    as Doc
import           Data.Traversable
import           GHC.TypeLits
import           PlutusPrelude                                (showText)



tweak :: Functor a => a () -> a Integer
tweak x = -1 <$ x
-- This is used to change annnotations from () to -1 in built-in constants

{- Note [Sequencing]
WARNING: it is not allowed to call 'eval' or @readKnown eval@ over a term that already
was 'eval'ed. It may be temptive to preevaluate to WHNF some term if you later need to evaluate
its several instantiations, but it is forbidden to do so. The reason for this restriction is that
'eval' encapsulates its internal state and the state gets updated during evaluation, so if you
try to call 'eval' over something that already was 'eval'ed, that second 'eval' won't have the
updated state that the first 'eval' finished with. This may cause all kinds of weird error messages,
for example, an error message saying that there is a free variable and evaluation cannot proceed.
-}

instance KnownType a => KnownType (EvaluationResult a) where
    toTypeAst _ = toTypeAst @a Proxy

    -- 'EvaluationFailure' on the Haskell side becomes 'Error' on the PLC side.
    makeKnown EvaluationFailure     = Error (-1) $ toTypeAst @a Proxy
    makeKnown (EvaluationSuccess x) = makeKnown x

    -- There are two 'EvaluationResult's here: an external one (which any 'KnownType'
    -- instance has to deal with) and an internal one (specific to this particular instance).
    -- Our approach is to always return 'EvaluationSuccess' for the external 'EvaluationResult'
    -- and catch all 'EvaluationFailure's in the internal 'EvaluationResult'.
    -- This allows *not* to short-circuit when 'readKnown' fails to read a Haskell value.
    -- Instead the user gets an explicit @EvaluationResult a@ and evaluation proceeds normally.
    readKnown eval = mapDeepReflectT (fmap $ EvaluationSuccess . sequence) . readKnown eval

    prettyKnown = pretty . fmap (PrettyConfigIgnore . KnownTypeValue)

instance (KnownSymbol text, KnownNat uniq) => KnownType (OpaqueTerm text uniq) where
    toTypeAst _ =
        TyVar (-1) . TyName $
            Name (-1)
                (Text.pack $ symbolVal @text Proxy)
                (Unique . fromIntegral $ natVal @uniq Proxy)

    makeKnown = unOpaqueTerm

    readKnown eval = (fmap OpaqueTerm) . makeRightReflectT . (eval mempty)

instance KnownType Integer where
    toTypeAst _ = TyBuiltin (-1) TyInteger

    makeKnown = Constant (-1) . makeBuiltinInt

    readKnown eval term = do
        -- 'term' is supposed to be already evaluated, but calling 'eval' is the easiest way
        -- to turn 'Error' into 'EvaluationFailure', which we later 'lift' to 'Convert'.
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant _ (BuiltinInt _ i) -> pure i
            _                           -> throwError "Not a builtin Integer"

instance KnownType Int where
    toTypeAst _ = TyBuiltin (-1) TyInteger

    makeKnown = Constant (-1) . makeBuiltinInt . fromIntegral

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            -- TODO: check that 'i' is in bounds.
            Constant _ (BuiltinInt _ i) -> pure $ fromIntegral i
            _                           -> throwError "Not a builtin Int"

instance KnownType BSL.ByteString where
    toTypeAst _ = TyBuiltin (-1) TyByteString

    makeKnown = Constant (-1) . makeBuiltinBS

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant _ (BuiltinBS _ i) -> pure i
            _                          -> throwError "Not a builtin ByteString"

    prettyKnown = prettyBytes

instance KnownType [Char] where
    toTypeAst _ = TyBuiltin (-1) TyString

    makeKnown = Constant (-1) . makeBuiltinStr

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant _ (BuiltinStr _ s) -> pure s
            _                           -> throwError "Not a builtin String"

instance KnownType Bool where
    toTypeAst _ = tweak bool

    makeKnown b = if b then tweak true else tweak false

    readKnown eval b = do
        let int = TyBuiltin (-1) TyInteger
            asInt = Constant (-1) . BuiltinInt (-1)
            -- Encode 'Bool' from Haskell as @integer 1@ from PLC.
            term = mkIterApp (-1) (TyInst (-1) b int) [asInt 1, asInt 0]
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant _ (BuiltinInt _ 1) -> pure True
            Constant _ (BuiltinInt _ 0) -> pure False
            _                           -> throwError "Not an integer-encoded Bool"

-- Encode 'Char' from Haskell as @integer@ from PLC.
instance KnownType Char where
    toTypeAst _ = TyBuiltin (-1) TyInteger

    makeKnown = Constant (-1) . makeBuiltinInt . fromIntegral . ord

    readKnown eval term = do
        res <- makeRightReflectT $ eval mempty term
        case res of
            Constant _ (BuiltinInt _ int) -> pure . chr $ fromIntegral int
            _                             -> throwError "Not an integer-encoded Char"

instance KnownType a => KnownType (() -> a) where
    toTypeAst _ = TyFun (-1) (tweak unit) $ toTypeAst @a Proxy

    -- Note that we can't just prepend a 'LamAbs' to the result due to name shadowing issues.
    makeKnown f =
        Apply (-1) (mkIterInst (-1) (tweak Plc.const) [da, tweak unit]) $ makeKnown $ f () where
            da = toTypeAst @a Proxy

    --        Apply () (mkIterInst () Plc.const [da, unit]) $ makeKnown $ f () where

    readKnown eval df = const <$> readKnown eval (Apply (-1) df (tweak unitval))

    prettyKnown f = "\\() ->" Doc.<+> prettyKnown (f ())

makeTypeAndKnown :: forall a. KnownType a => a -> (Type TyName Integer, Term TyName Name Integer)
makeTypeAndKnown x = (da, dx) where
    da = toTypeAst @a Proxy
    dx = makeKnown x

instance (KnownType a, KnownType b) => KnownType (a, b) where
    toTypeAst _ =
        mkIterTyApp (-1) (tweak $ prodN 2)
            [ toTypeAst @a Proxy
            , toTypeAst @b Proxy
            ]

    makeKnown (x, y) = _tupleTerm . runQuote $ getSpineToTuple (-1) [dax, dby] where
        dax = makeTypeAndKnown x
        dby = makeTypeAndKnown y

    readKnown eval dxy = do
        let da = toTypeAst @a Proxy
            db = toTypeAst @b Proxy
            prodNAccessorInst i = mkIterInst (-1) (tweak $ prodNAccessor 2 i) [da, db]
        -- Read elements of the tuple separately.
        x <- readKnown eval $ Apply (-1) (prodNAccessorInst 0) dxy
        y <- readKnown eval $ Apply (-1) (prodNAccessorInst 1) dxy
        pure (x, y)

    prettyKnown = pretty . bimap KnownTypeValue KnownTypeValue

-- From Meta.hs

left2 :: TermLike term TyName Name => term Integer
left2 = runQuote $ do
    a <- freshTyName (-1) "a"
    b <- freshTyName (-1) "b"
    x <- freshName (-1) "x"
    r <- freshTyName (-1) "r"
    f <- freshName (-1) "f"
    g <- freshName (-1) "g"
    return
        . tyAbs (-1) a (Type (-1))
        . tyAbs (-1) b (Type (-1))
        . lamAbs (-1) x (TyVar (-1) a)
        . tyAbs (-1) r (Type (-1))
        . lamAbs (-1) f (TyFun (-1) (TyVar (-1) a) $ TyVar (-1) r)
        . lamAbs (-1) g (TyFun (-1) (TyVar (-1) b) $ TyVar (-1) r)
        . apply (-1) (var (-1) f)
        $ var (-1) x

-- | 'Right' as a PLC term.
--
-- > /\(a b :: *) -> \(y : b) -> /\(r :: *) -> \(f : a -> r) -> (g : b -> r) -> g y
right2 :: TermLike term TyName Name => term Integer
right2 = runQuote $ do
    a <- freshTyName (-1) "a"
    b <- freshTyName (-1) "b"
    y <- freshName (-1) "y"
    r <- freshTyName (-1) "r"
    f <- freshName (-1) "f"
    g <- freshName (-1) "g"
    return
        . tyAbs (-1) a (Type (-1))
        . tyAbs (-1) b (Type (-1))
        . lamAbs (-1) y (TyVar (-1) b)
        . tyAbs (-1) r (Type (-1))
        . lamAbs (-1) f (TyFun (-1) (TyVar (-1) a) $ TyVar (-1) r)
        . lamAbs (-1) g (TyFun (-1) (TyVar (-1) b) $ TyVar (-1) r)
        . apply (-1) (var (-1) g)
        $ var (-1) y

metaEitherToSum2  --- Copied from Meta.hs
    :: TermLike term TyName Name
    => Type TyName Integer
    -> Type TyName Integer
    -> Either (term Integer) (term Integer)
    -> term Integer

metaEitherToSum2 a b (Left  x) = apply (-1) (mkIterInst (-1) left2  [a, b]) x
metaEitherToSum2 a b (Right y) = apply (-1) (mkIterInst (-1) right2 [a, b]) y


instance (KnownType a, KnownType b) => KnownType (Either a b) where
    toTypeAst _ =
        mkIterTyApp (-1) (tweak Plc.sum)
            [ toTypeAst @a Proxy
            , toTypeAst @b Proxy
            ]

    makeKnown s = metaEitherToSum2 da db ds where
        da = toTypeAst @a Proxy
        db = toTypeAst @b Proxy
        ds = bimap makeKnown makeKnown s

    -- At first I tried this representation:
    --
    -- > ds {((-1) -> a, (-1) -> b)}
    -- >     (\(x : a) -> (\_ -> x        , \_ -> error {b}))
    -- >     (\(y : b) -> (\_ -> error {a}, \_ -> y        ))
    --
    -- but it didn't work, because here the type of the result always contains both 'a' and 'b',
    -- so values of both of the types are attempted to be extracted via 'readKnown'
    -- which causes a loop when we need to read lists back, because in the nil case we attempt to
    -- read both branches of an 'Either' and one of them is supposed to be a list and the fact
    -- that it's actually an 'Error' does not help, because 'readKnown' is still called
    -- recursively where it shouldn't.
    --
    -- So the actual implementation is: first figure out whether the 'sum' is 'left' or 'right' via
    --
    -- > ds {bool} (\(x : a) -> true) (\(y : b) -> false)
    --
    -- and depending on the result call either
    --
    -- > ds {a} (\(x : a) -> x) (\(y : b) -> error {a})
    --
    -- or
    --
    -- > ds {b} (\(x : a) -> error {b}) (\(y : b) -> y)
    readKnown eval ds = undefined
                        {- do
        let da = toTypeAst @a Proxy
            db = toTypeAst @b Proxy
            branch = runQuote $ do
                x <- freshName (-1) "x"
                y <- freshName (-1) "y"
                pure $ mkIterApp (-1) (TyInst (-1) (tweak ds) (tweak bool))
                    [ LamAbs (-1) x da (tweak true)
                    , LamAbs (-1) y db (tweak false)
                    ]
        isL <- readKnown eval branch
        let term = runQuote $ do
                x <- freshName (-1) "x"
                y <- freshName (-1) "y"
                pure $ if isL
                    then mkIterApp (-1) (TyInst (-1) ds da)
                        [ LamAbs (-1) x da $ Var (-1) x
                        , LamAbs (-1) y db $ Error (-1) da
                        ]
                    else mkIterApp (-1) (TyInst (-1) ds db)
                        [ LamAbs (-1) x da $ Error (-1) db
                        , LamAbs (-1) y db $ Var (-1) y
                        ]
        if isL
            then Left  <$> readKnown eval term
            else Right <$> readKnown eval term
-}
    prettyKnown = either prettyKnown prettyKnown


newtype PlcList a = PlcList
    { unPlcList :: [a]
    } deriving (Eq, Show)

-- > fix \(list :: * -> *) (a :: *) -> all (r :: *). r -> (a -> list a -> r) -> r
listData2 :: RecursiveType Integer
listData2 = runQuote $ do
    a    <- freshTyName (-1) "a"
    list <- freshTyName (-1) "list"
    r    <- freshTyName (-1) "r"
    let listA = TyApp (-1) (TyVar (-1) list) (TyVar (-1) a)
    makeRecursiveType (-1) list [TyVarDecl (-1) a $ Type (-1)]
        . TyForall (-1) r (Type (-1))
        . TyFun (-1) (TyVar (-1) r)
        . TyFun (-1) (TyFun (-1) (TyVar (-1) a) . TyFun (-1) listA $ TyVar (-1) r)
        $ TyVar (-1) r


-- >  /\(a :: *) -> wrapList [a] /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> z)
nil2 :: TermLike term TyName Name => term Integer
nil2 = runQuote $ do
    let RecursiveType list wrapList = listData2
    a <- freshTyName (-1) "a"
    r <- freshTyName (-1) "r"
    z <- freshName (-1) "z"
    f <- freshName (-1) "f"
    let listA = TyApp (-1) list (TyVar (-1) a)
    return
        . tyAbs (-1) a (Type (-1))
        . wrapList [TyVar (-1) a]
        . tyAbs (-1) r (Type (-1))
        . lamAbs (-1) z (TyVar (-1) r)
        . lamAbs (-1) f (TyFun (-1) (TyVar (-1) a) . TyFun (-1) listA $ TyVar (-1) r)
        $ var (-1) z

-- |  '(:)' as a PLC term.
--
-- > /\(a :: *) -> \(x : a) (xs : list a) ->
-- >     wrapList [a] /\(r :: *) -> \(z : r) (f : a -> list a -> r) -> f x xs
cons2 :: TermLike term TyName Name => term Integer
cons2 = runQuote $ do
    let RecursiveType list wrapList = listData2
    a  <- freshTyName (-1) "a"
    x  <- freshName (-1) "x"
    xs <- freshName (-1) "xs"
    r  <- freshTyName (-1) "r"
    z  <- freshName (-1) "z"
    f  <- freshName (-1) "f"
    let listA = TyApp (-1) list (TyVar (-1) a)
    return
        . tyAbs (-1) a (Type (-1))
        . lamAbs (-1) x (TyVar (-1) a)
        . lamAbs (-1) xs listA
        . wrapList [TyVar (-1) a]
        . tyAbs (-1) r (Type (-1))
        . lamAbs (-1) z (TyVar (-1) r)
        . lamAbs (-1) f (TyFun (-1) (TyVar (-1) a) . TyFun (-1) listA $ TyVar (-1) r)
        $ mkIterApp (-1) (var (-1) f)
          [ var (-1) x
          , var (-1) xs
          ]



metaListToList2 :: TermLike term TyName Name => Type TyName Integer -> [term Integer] -> term Integer
metaListToList2 ty =
    foldr
        (\x xs -> mkIterApp (-1) (tyInst (-1) cons2 ty) [x, xs])
        (tyInst (-1) nil2 ty)


prodNConstructor2 :: TermLike term TyName Name => Int -> term Integer
prodNConstructor2 arity = runQuote $ do
    tyVars <- for [0..(arity-1)] $ \i -> do
        tn <- liftQuote $ freshTyName (-1) $ "t_" <> showText i
        pure $ TyVarDecl (-1) tn $ Type (-1)

    resultType <- liftQuote $ freshTyName (-1) "r"

    args <- for [0..(arity -1)] $ \i -> do
        n <- liftQuote $ freshName (-1) $ "arg_" <> showText i
        pure $ VarDecl (-1) n $ mkTyVar (-1) $ tyVars !! i

    caseArg <- liftQuote $ freshName (-1) "case"
    let caseTy = mkIterTyFun (-1) (fmap (mkTyVar (-1)) tyVars) (TyVar (-1) resultType)
    pure $
        -- /\T_1 .. T_n
        mkIterTyAbs tyVars $
        -- \arg_1 .. arg_n
        mkIterLamAbs args $
        -- /\R
        tyAbs (-1) resultType (Type (-1)) $
        -- \case
        lamAbs (-1) caseArg caseTy $
        -- case arg_1 .. arg_n
        mkIterApp (-1) (var (-1) caseArg) $ fmap (mkVar (-1)) args



instance KnownType a => KnownType (PlcList a) where
    toTypeAst _ = TyApp (-1) (_recursiveType listData2) $ toTypeAst (Proxy @a)

    makeKnown (PlcList xs) = metaListToList2 argTy dyns where
        dyns = map makeKnown xs
        argTy = toTypeAst @a Proxy

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
    -- of the list. That is, we implicitly invoke 'readKnown' recursively until the list
    -- is empty.
    readKnown eval list =
        do
        let term = runQuote $ do
                -- > unwrap list {sum unit (prodN 2 a (list a))} unitval
                -- >     \(x : a) (xs : list a) -> prodNConstructor 2 {a} {list a} x xs
                let listA = toTypeAst @(PlcList a) Proxy
                    a     = toTypeAst @a           Proxy
                    resL =  tweak unit
                    resR = mkIterTyApp (-1) (tweak $ prodN 2) [a, listA]
                    -- TODO: use 'maybe' instead of 'sum'.
                    res  = mkIterTyApp (-1) (tweak Plc.sum) [resL, resR]
                x  <- freshName (-1) "x"
                xs <- freshName (-1) "xs"
                pure $ mkIterApp (-1) (TyInst (-1) (Unwrap (-1) list) res)
                    [ Apply (-1) (mkIterInst (-1) left2 [ resL,  resR]) (tweak unitval)
                    ,   LamAbs (-1) x  a
                      . LamAbs (-1) xs listA
                      . Apply (-1) (mkIterInst (-1) right2 [ resL,  resR])
                      $ mkIterApp (-1) (mkIterInst (-1) (prodNConstructor2 2) [a, listA])
                          [ Var (-1) x, Var (-1) xs ]
                    ]
        res <- readKnown eval term
        pure . PlcList $ case res of
            Left  ()              -> []
            Right (x, PlcList xs) -> x : xs

    prettyKnown = pretty . map KnownTypeValue . unPlcList
