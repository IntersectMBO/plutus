-- | Generators of various PLC things: 'Builtin's, 'IterApp's, 'Term's, etc.

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Generators.Internal.Entity
    ( PlcGenT
    , IterAppValue(..)
    , runPlcT
    , withTypedBuiltinGen
    , withCheckedTermGen
    , genIterAppValue
    , genTerm
    , genTermLoose
    , withAnyTermLoose
    ) where

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Generators.Internal.Denotation
import           Language.PlutusCore.Generators.Internal.Dependent
import           Language.PlutusCore.Generators.Internal.TypedBuiltinGen
import           Language.PlutusCore.Generators.Internal.TypeEvalCheck
import           Language.PlutusCore.Generators.Internal.Utils
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           Language.PlutusCore.View
import           PlutusPrelude

import           Control.Exception                                       (evaluate)
import           Control.Exception.Safe                                  (tryAny)
import qualified Control.Monad.Morph                                     as Morph
import           Control.Monad.Reader
import           Control.Monad.Trans.Class                               (lift)
import qualified Data.ByteString.Lazy                                    as BSL
import qualified Data.Dependent.Map                                      as DMap
import           Data.Functor.Compose
import           Data.Proxy
import           Data.Text.Prettyprint.Doc
import           Hedgehog                                                hiding (Size, Var)
import qualified Hedgehog.Gen                                            as Gen
import           System.IO.Unsafe

-- | Generators of built-ins supplied to computations that run in the 'PlcGenT' monad.
newtype BuiltinGensT m = BuiltinGensT
    { _builtinGensTyped :: TypedBuiltinGenT m  -- ^ Generates a PLC 'Term' and the corresponding
                                               -- Haskell value out of a 'TypedBuiltin'.
    }

-- | The type used in generators defined in this module.
-- It's parameterized by a 'BuiltinGensT' which makes it possible to supply
-- different generators of built-in types. For example, 'genTypedBuiltinDiv'
-- never generates a zero, so this generator can be used in order to avoid the
-- divide-by-zero-induced @error@. Supplied generators are of arbitrary complexity
-- and can call the currently running generator recursively, for example.
type PlcGenT m = GenT (ReaderT (BuiltinGensT m) m)

-- | One iterated application of a @head@ to @arg@s represented in three distinct ways.
data IterAppValue head arg r = IterAppValue
    { _iterTerm :: Term TyName Name ()  -- ^ As a PLC 'Term'.
    , _iterApp  :: IterApp head arg     -- ^ As an 'IterApp'.
    , _iterTbv  :: r                    -- ^ As a Haskell value.
    }

instance ( PrettyBy config (Term TyName Name ())
         , PrettyBy config head, PrettyBy config arg, KnownType r
         ) => PrettyBy config (IterAppValue head arg r) where
    prettyBy config (IterAppValue term pia y) = parens $ fold
        [ "{ ", prettyBy config term, line
        , "| ", prettyBy config pia, line
        , "| ", prettyKnown y, line
        , "}"
        ]

-- | Run a 'PlcGenT' computation by supplying built-ins generators.
runPlcT :: Monad m => TypedBuiltinGenT m -> PlcGenT m a -> GenT m a
runPlcT genTb = hoistSupply $ BuiltinGensT genTb

-- | Get a 'TermOf' out of an 'IterAppValue'.
iterAppValueToTermOf :: IterAppValue head arg r -> TermOf r
iterAppValueToTermOf (IterAppValue term _ y) = TermOf term y

-- | Add to the 'ByteString' representation of a 'Name' its 'Unique'
-- without any additional symbols inbetween.
revealUnique :: Name a -> Name a
revealUnique (Name ann name uniq) =
    Name ann (name <> prettyText (unUnique uniq)) uniq

-- TODO: we can generate more types here: @uni@, @maybe@, @list@, etc -- basically any 'KnownType'.
-- | Generate a 'Builtin' and supply its typed version to a continuation.
withTypedBuiltinGen :: Monad m => (forall a. AsKnownType a -> GenT m c) -> GenT m c
withTypedBuiltinGen k = Gen.choice
    [ k @Integer        AsKnownType
    , k @BSL.ByteString AsKnownType
    , k @Bool           AsKnownType
    ]

-- | Generate a 'Term' along with the value it computes to,
-- having a generator of terms of built-in types.
withCheckedTermGen
    :: Monad m
    => TypedBuiltinGenT m
    -> (forall a. AsKnownType a -> Maybe (TermOf (Value TyName Name ())) -> GenT m c)
    -> GenT m c
withCheckedTermGen genTb k =
    withTypedBuiltinGen $ \akt@AsKnownType -> do
        termWithMetaValue <- genTb akt
        let mayTermWithValue = unsafeTypeEvalCheck termWithMetaValue
        k akt mayTermWithValue

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
    => Denotation head r
    -> PlcGenT m (IterAppValue head (Term TyName Name ()) r)
genIterAppValue (Denotation object toTerm meta scheme) = result where
    result = Gen.just $ go scheme (toTerm object) id meta

    go
        :: TypeScheme c r
        -> Term TyName Name ()
        -> ([Term TyName Name ()] -> [Term TyName Name ()])
        -> c
        -> PlcGenT m (Maybe (IterAppValue head (Term TyName Name ()) r))
    go (TypeSchemeResult _)       term args y =     -- Computed the result.
        -- TODO: there should never be any exceptions, fix this.
        return $ case unsafePerformIO . tryAny $ evaluate y of
            Left _   -> Nothing
            Right y' -> do
                let pia = IterApp object $ args []
                return $ IterAppValue term pia y'
    go (TypeSchemeArrow _ schB)   term args f = do  -- Another argument is required.
        BuiltinGensT genTb <- ask
        TermOf v x <- liftT $ genTb AsKnownType  -- Get a Haskell and the correspoding PLC values.
        let term' = Apply () term v              -- Apply the term to the PLC value.
            args' = args . (v :)                 -- Append the PLC value to the spine.
            y     = f x                          -- Apply the Haskell function to the generated argument.
        go schB term' args' y
    go (TypeSchemeAllType _ schK) term args f =
        go (schK Proxy) term args f

-- | Generate a PLC 'Term' of the specified type and the corresponding Haskell value.
-- Generates first-order functions and constants including constant applications.
-- Arguments to functions and 'BuiltinName's are generated recursively.
genTerm
    :: forall m. Monad m
    => TypedBuiltinGenT m      -- ^ Ground generators of built-ins. The base case of the recursion.
    -> DenotationContext       -- ^ A context to generate terms in. See for example 'typedBuiltinNames'.
                               -- Gets extended by a variable when an applied lambda is generated.
    -> Int                     -- ^ Depth of recursion.
    -> TypedBuiltinGenT m
genTerm genBase context0 depth0 = Morph.hoist runQuoteT . go context0 depth0 where
    go :: DenotationContext -> Int -> AsKnownType r -> GenT (QuoteT m) (TermOf r)
    go context depth akt
        -- FIXME: should be using 'variables' but this is now the same as 'recursive'
        | depth == 0 = choiceDef (liftT $ genBase akt) []
        | depth == 1 = choiceDef (liftT $ genBase akt) $ variables ++ recursive
        | depth == 2 = Gen.frequency $ stopOrDeeper ++ map (3 ,) variables ++ map (5 ,) recursive
        | depth == 3 = Gen.frequency $ stopOrDeeper ++ map (3 ,) recursive
        | otherwise  = Gen.frequency stopOrDeeper
        where
            stopOrDeeper = [(1, liftT $ genBase akt), (5, lambdaApply)]
            -- Generators of built-ins to feed them to 'genIterAppValue'.
            -- Note that the typed built-ins generator calls 'go' recursively.
            builtinGens = BuiltinGensT (flip Gen.subterm id . go context (depth - 1))
            -- Generate arguments for functions recursively or return a variable.
            proceed (DenotationContextMember denotation) =
                fmap iterAppValueToTermOf . hoistSupply builtinGens $ genIterAppValue denotation
            -- Look up a list of 'Denotation's from 'DenotationContext' each of which
            -- has a type that ends in the same type as the one that 'tb\'' represents.
            lookupInContext tb' = foldMap getCompose . DMap.lookup tb' $ unDenotationContext context
            -- A list of variables generators.
            variables = map proceed $ lookupInContext akt
            -- A list of recursive generators.
            recursive = map proceed $ lookupInContext akt
            -- Generate a lambda and immediately apply it to a generated argument of a generated type.
            lambdaApply = withTypedBuiltinGen $ \argKt@AsKnownType -> do
                -- Generate a name for the name representing the argument.
                name  <- lift $ revealUnique <$> freshName () "x"
                -- Get the 'Type' of the argument from a generated 'TypedBuiltin'.
                let argTy = toTypeAst argKt
                -- Generate the argument.
                TermOf arg  x <- go context (depth - 1) argKt
                -- Generate the body of the lambda abstraction adding the new variable to the context.
                TermOf body y <- go (insertVariable name x context) (depth - 1) akt
                -- Assemble the term.
                let term = Apply () (LamAbs () name argTy body) arg
                return $ TermOf term y

-- | Generates a 'Term' with rather small values to make out-of-bounds failures less likely.
-- There are still like a half of terms that fail with out-of-bounds errors being evaluated.
genTermLoose :: Monad m => TypedBuiltinGenT m
genTermLoose = genTerm genTypedBuiltinDef typedBuiltinNames 4

-- | Generate a 'TypedBuiltin' and a 'TermOf' of the corresponding type,
-- attach the 'TypedBuiltin' to the value part of the 'TermOf' and pass that to a continuation.
withAnyTermLoose :: Monad m => (forall a. KnownType a => TermOf a -> GenT m c) -> GenT m c
withAnyTermLoose k = withTypedBuiltinGen $ \akt@AsKnownType -> genTermLoose akt >>= k
