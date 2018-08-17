{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
module Evaluation.Generator
    ( min_size
    , max_size
    , PlcGenT
    , IterAppValue(..)
    , forAllPretty
    , forAllPrettyT
    , hoistSupply
    , genSizeIn
    , genSizeDef
    , denoteTypedBuiltinName
    , runPlcT
    , genIterAppValue
    , genTerm
    , genTermLoose
    ) where

import           PlutusPrelude
import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Evaluation.Denotation
import           Evaluation.Constant.TypedBuiltinGen

import           Data.Functor.Compose
import           Data.String
import           Control.Exception (evaluate)
import           Control.Exception.Safe (tryAny)
import           Control.Monad.Reader
import           Control.Monad.Morph
import           Data.Text.Prettyprint.Doc
import qualified Data.Dependent.Map as DMap
import           Hedgehog hiding (Size, Var, annotate)
import           Hedgehog.Internal.Property (forAllWithT)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range
import           System.IO.Unsafe

min_size :: Size
min_size = 1

max_size :: Size
max_size = 2

liftT :: (MFunctor t, MonadTrans s, Monad m) => t m a -> t (s m) a
liftT = hoist lift

forAllPretty :: (Monad m, Pretty a) => Gen a -> PropertyT m a
forAllPretty = forAllWith prettyString

forAllPrettyT :: (Monad m, Pretty a) => GenT m a -> PropertyT m a
forAllPrettyT = forAllWithT prettyString

hoistSupply :: (MFunctor t, Monad m) => r -> t (ReaderT r m) a -> t m a
hoistSupply r = hoist $ flip runReaderT r

choiceDef :: Monad m => GenT m a -> [GenT m a] -> GenT m a
choiceDef a [] = a
choiceDef _ as = Gen.choice as

genSizeIn :: Monad m => Size -> Size -> GenT m Size
genSizeIn = Gen.integral .* Range.linear

genSizeDef :: Monad m => GenT m Size
genSizeDef = genSizeIn min_size max_size

genSizeFrom :: Monad m => TypedBuiltin Size a -> GenT m Size
genSizeFrom (TypedBuiltinSized sizeEntry _) = return $ flattenSizeEntry sizeEntry
genSizeFrom TypedBuiltinBool                = genSizeDef

genBuiltinSized :: Monad m => GenT m BuiltinSized
genBuiltinSized = Gen.element [BuiltinSizedInt, BuiltinSizedBS, BuiltinSizedSize]

genBuiltin :: Monad m => GenT m (Builtin size)
genBuiltin =
    BuiltinSized . SizeValue <$> genSizeDef <*> genBuiltinSized <|> return BuiltinBool

withTypedBuiltinGen :: Monad m => (forall a. TypedBuiltin size a -> GenT m c) -> GenT m c
withTypedBuiltinGen k = genBuiltin >>= \b -> withTypedBuiltin b k

data BuiltinGensT m = BuiltinGensT
    { _builtinGensSize  :: GenT m Size
    , _builtinGensTyped :: TypedBuiltinGenT m
    }

-- | The type used in generators defined in this module.
-- It is parameterized by an 'TheTypedBuiltinGen' which determines
-- how to generate sized builtins having a 'Size'. See for example
-- 'genTypedBuiltinSum' and 'genTypedBuiltinDiv'.
type PlcGenT m = GenT (ReaderT (BuiltinGensT m) m)

-- | One iterated application of a @head@ to @arg@s represented in three distinct ways.
data IterAppValue head arg r = IterAppValue
    (Term TyName Name ())       -- ^ As a PLC 'Term'.
    (IterApp head arg)          -- ^ As an 'IterApp'.
    (TypedBuiltinValue Size r)  -- ^ As a Haskell value.

instance (Pretty head, Pretty arg) => Pretty (IterAppValue head arg r) where
    pretty (IterAppValue term pia tbv) = parens $ mconcat
        [ "{ ", pretty term, line
        , "| ", pretty pia, line
        , "| ", pretty tbv, line
        , "}"
        ]

runPlcT :: Monad m => GenT m Size -> TypedBuiltinGenT m -> PlcGenT m a -> GenT m a
runPlcT genSize genTb = hoistSupply $ BuiltinGensT genSize genTb

iterAppValueToTermOf :: IterAppValue head arg r -> TermOf r
iterAppValueToTermOf (IterAppValue term _ (TypedBuiltinValue _ x)) = TermOf term x

-- | Generate a value out of a 'TypeScheme' and return it along with the corresponding PLC value.
genSchemedTermOf :: Monad m => TypeScheme Size a r -> PlcGenT m (TermOf a)
genSchemedTermOf (TypeSchemeBuiltin tb) = do
    BuiltinGensT _ genTb <- ask
    liftT $ genTb tb
genSchemedTermOf (TypeSchemeArrow _ _)  = error "Not implemented."
genSchemedTermOf (TypeSchemeAllSize _)  = error "Not implemented."

genIterAppValue
    :: forall head r m. Monad m
    => Denotation head Size r
    -> PlcGenT m (IterAppValue head (Term TyName Name ()) r)
genIterAppValue (Denotation object toTerm meta scheme) = Gen.just $ go scheme (toTerm object) id meta where
    go
        :: TypeScheme Size c r
        -> Term TyName Name ()
        -> ([Term TyName Name ()] -> [Term TyName Name ()])
        -> c
        -> PlcGenT m (Maybe (IterAppValue head (Term TyName Name ()) r))
    go (TypeSchemeBuiltin builtin) term args y = do  -- Computed the result.
        return $ case unsafePerformIO . tryAny $ evaluate y of
            Left _   -> Nothing
            Right y' -> do
                let pia = IterApp object $ args []
                    tbv = TypedBuiltinValue builtin y'
                return $ IterAppValue term pia tbv
    go (TypeSchemeArrow schA schB) term args f = do  -- Another argument is required.
        TermOf v x <- genSchemedTermOf schA          -- Get a Haskell and the correspoding PLC values.

        let term' = Apply () term v                  -- Apply the term to the PLC value.
            args' = args . (v :)                     -- Append the PLC value to the spine.
            y     = f x                              -- Apply the Haskell function to the generated argument.
        go schB term' args' y
    go (TypeSchemeAllSize schK)    term args f = do
        BuiltinGensT genSize _ <- ask
        size <- liftT genSize                        -- Generate a size.
        let term' = TyInst () term $ TyInt () size   -- Instantiate the term with the generated size.
        go (schK size) term' args f                  -- Instantiate a size variable with the generated size.

genTerm
    :: TypedBuiltinGenT Fresh -> Context -> Int -> TypedBuiltin Size r -> GenT Fresh (TermOf r)
genTerm genBase = go where
    go :: Context -> Int -> TypedBuiltin Size r -> GenT Fresh (TermOf r)
    go context depth tb
        | depth == 0 = choiceDef (genBase tb) variables
        | depth == 1 = choiceDef (genBase tb) $ variables ++ recursive
        | depth == 2 = Gen.choice $ lambdaApply : variables ++ recursive
        | depth == 3 = Gen.choice $ lambdaApply : recursive
        | otherwise  = lambdaApply
        where
            desizedTb = mapSizeEntryTypedBuiltin (\_ -> SizeBound ()) tb
            builtinGens = BuiltinGensT (genSizeFrom tb) (flip Gen.subterm id . go context (depth - 1))
            recurse (MemberDenotation denotation) =
                fmap iterAppValueToTermOf . hoistSupply builtinGens $ genIterAppValue denotation
            lookupInContext tb' = foldMap getCompose . DMap.lookup tb' $ unContext context
            variables = map recurse . lookupInContext $ closeTypedBuiltin tb
            recursive = map recurse $ lookupInContext desizedTb
            lambdaApply = withTypedBuiltinGen $ \argTb -> do
                -- TODO: 'freshInt' is not supposed to be here.
                name <- lift $ freshInt >>= \i -> freshName () $ "x" <> fromString (show i)
                let argTyTb = mapSizeTypedBuiltin (\_ -> TyBuiltin () TySize) argTb
                argTy <- lift $ typedBuiltinToType argTyTb
                TermOf arg  x <- go context (depth - 1) argTb
                TermOf body y <- go (insertVariable name argTb x context) (depth - 1) tb
                let term = Apply () (LamAbs () name argTy body) arg
                return $ TermOf term y

genTermLoose :: TypedBuiltinGenT Fresh
genTermLoose = genTerm genTypedBuiltinLoose typedBuiltinNames 4

-- getTerm :: IO ()
-- getTerm = do
--     tx <- Gen.sample . hoist (return . dropFresh) $
--               genTermLoose $ TypedBuiltinSized (SizeValue 2) TypedBuiltinSizedInt
--     putStrLn $ prettyString tx
