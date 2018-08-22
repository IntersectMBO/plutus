{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
module Evaluation.Generator
    ( PlcGenT
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
import qualified Data.ByteString.Lazy.Char8 as BSL
import           Data.Text.Prettyprint.Doc
import qualified Data.Dependent.Map as DMap
import           Hedgehog hiding (Size, Var, annotate)
import           Hedgehog.Internal.Property (forAllWithT)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range
import           System.IO.Unsafe

liftT :: (MFunctor t, MonadTrans s, Monad m) => t m a -> t (s m) a
liftT = hoist lift

choiceDef :: Monad m => GenT m a -> [GenT m a] -> GenT m a
choiceDef a [] = a
choiceDef _ as = Gen.choice as

forAllPretty :: (Monad m, Pretty a) => Gen a -> PropertyT m a
forAllPretty = forAllWith prettyString

forAllPrettyT :: (Monad m, Pretty a) => GenT m a -> PropertyT m a
forAllPrettyT = forAllWithT prettyString

hoistSupply :: (MFunctor t, Monad m) => r -> t (ReaderT r m) a -> t m a
hoistSupply r = hoist $ flip runReaderT r

revealUnique :: Name a -> Name a
revealUnique (Name ann name uniq) = Name ann (name <> BSL.pack ('_' : show uniq)) uniq

genSizeIn :: Monad m => Size -> Size -> GenT m Size
genSizeIn = Gen.integral .* Range.linear

genSizeDef :: Monad m => GenT m Size
genSizeDef = genSizeIn 1 3

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

-- | Generators of built-ins supplied to computations that run in the 'PlcGenT' monad.
data BuiltinGensT m = BuiltinGensT
    { _builtinGensSize  :: GenT m Size         -- ^ Generates a 'Size'.
    , _builtinGensTyped :: TypedBuiltinGenT m  -- ^ Generates a PLC 'Term' and the corresponding
                                               -- Haskell value out of a 'TypedBuiltin'.
    }

-- | The type used in generators defined in this module.
-- It's parameterized by a 'BuiltinGensT' which makes it possible to supply
-- different generators of built-in types. For example, 'genTypedBuiltinDiv'
-- never generates a zero, so this generator can be used in order to avoid the
-- divide-by-zero exception. Supplied generators are of arbitrary complexity
-- and can call the currently running generator recursively, for example.
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

-- | Run a 'PlcGenT' computation by supplying built-ins generators.
runPlcT :: Monad m => GenT m Size -> TypedBuiltinGenT m -> PlcGenT m a -> GenT m a
runPlcT genSize genTb = hoistSupply $ BuiltinGensT genSize genTb

-- | Get a 'TermOf' out of an 'IterAppValue'.
iterAppValueToTermOf :: IterAppValue head arg r -> TermOf r
iterAppValueToTermOf (IterAppValue term _ (TypedBuiltinValue _ x)) = TermOf term x

-- | Generate a 'TermOf' out of a 'TypeScheme'.
genSchemedTermOf :: Monad m => TypeScheme Size a r -> PlcGenT m (TermOf a)
genSchemedTermOf (TypeSchemeBuiltin tb) = do
    BuiltinGensT _ genTb <- ask
    liftT $ genTb tb
genSchemedTermOf (TypeSchemeArrow _ _)  = error "Not implemented."
genSchemedTermOf (TypeSchemeAllSize _)  = error "Not implemented."

-- | Generate an 'IterAppValue' from a 'Denotation'.
-- If the 'Denotation' has a functional type, then all arguments are generated and
-- supplied to the denotation, the resulting value is forced and if there are any exceptions,
-- then all generated arguments are discarded and another attempt is performed
-- (this process does not loop). Since 'IterAppValue' consists of three components, we
--   1. grow the 'Term' component by applying it to arguments using 'Apply'
--   2. grow the 'IterApp' component by appending arguments to its spine
--   3. feed arguments to the Haskell function
genIterAppValue
    :: forall head r m. Monad m
    => Denotation head Size r
    -> PlcGenT m (IterAppValue head (Term TyName Name ()) r)
genIterAppValue (Denotation object toTerm meta scheme) = result where
    result = Gen.just $ go scheme (toTerm object) id meta

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

-- | Generate a PLC 'Term' and the corresponding Haskell value.
genTerm
    :: TypedBuiltinGenT Fresh  -- ^ Ground generators of built-ins. The base case of the recursion.
    -> DenotationContext       -- ^ A context to generate terms in. See for example 'typedBuiltinNames'.
                               -- Gets extended by a variable when an applied lambda is generated.
    -> Int                     -- ^ Depth of recursion.
    -> TypedBuiltin Size r     -- ^ Determines the resulting type.
    -> GenT Fresh (TermOf r)
genTerm genBase = go where
    go :: DenotationContext -> Int -> TypedBuiltin Size r -> GenT Fresh (TermOf r)
    go context depth tb
        | depth == 0 = choiceDef (genBase tb) variables
        | depth == 1 = choiceDef (genBase tb) $ variables ++ recursive
        | depth == 2 = Gen.choice $ lambdaApply : variables ++ recursive
        | depth == 3 = Gen.choice $ lambdaApply : recursive
        | otherwise  = lambdaApply
        where
            -- Instantiate all size variables with `()`.
            desizedTb = mapSizeEntryTypedBuiltin (\_ -> SizeBound ()) tb
            -- Generators of built-ins to feed them to 'genIterAppValue'.
            -- Note that we currently generate the same size over and over again (see 'genSizeFrom').
            -- We could also generate distinct sizes and use 'ResizeInteger'. That's a TODO probably.
            -- Generating size variables would be nice too, but that's too complicated.
            -- Note that the typed built-ins generator calls 'go' recursively.
            builtinGens = BuiltinGensT (genSizeFrom tb) (flip Gen.subterm id . go context (depth - 1))
            -- Generate arguments for functions recursively or return a variable.
            proceed (DenotationContextMember denotation) =
                fmap iterAppValueToTermOf . hoistSupply builtinGens $ genIterAppValue denotation
            -- Look up a list of 'Denotation's from 'DenotationContext' each of which
            -- has a type that ends in the same type as the one that 'tb\'' represents.
            lookupInContext tb' = foldMap getCompose . DMap.lookup tb' $ unDenotationContext context
            -- A list of variables generators.
            variables = map proceed . lookupInContext $ closeTypedBuiltin tb
            -- A list of recursive generators. We use 'desizedTb' instead of just 'tb'
            -- in order to make e.g. 'integer 2' unifiable with 'integer s' for universally
            -- quantified 's'. For this we simply instantiate all variables with '()' in
            -- the type, a term of which we're currently generating, and look that type up in
            -- the current context where universally quantified variable are already
            -- instantiate to '()' (which happens at the insertion phase, see ')
            recursive = map proceed $ lookupInContext desizedTb
            lambdaApply = withTypedBuiltinGen $ \argTb -> do
                let argTyTb = mapSizeTypedBuiltin (\_ -> TyBuiltin () TySize) argTb
                name  <- lift $ revealUnique <$> freshName () "x"
                argTy <- lift $ typedBuiltinToType argTyTb
                TermOf arg  x <- go context (depth - 1) argTb
                TermOf body y <- go (insertVariable name argTb x context) (depth - 1) tb
                let term = Apply () (LamAbs () name argTy body) arg
                return $ TermOf term y

genTermLoose :: TypedBuiltinGenT Fresh
genTermLoose = genTerm genTypedBuiltinLoose typedBuiltinNames 4
