{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings   #-}
module Evaluation.Generator
    ( GenPlcT
    , IterAppValue(..)
    , max_size
    , hoistSupply
    , denoteTypedBuiltinName
    , genSizeDef
    , runPlcT
    , genIterAppValue
    , genTerm
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Evaluation.Denotation
import           Evaluation.Constant.GenTypedBuiltin

import           Data.Functor.Compose
import           Control.Exception (evaluate)
import           Control.Exception.Safe (tryAny)
import           Control.Monad.Reader
import           Control.Monad.Morph
import           Data.Text.Prettyprint.Doc
import qualified Data.Dependent.Map as DMap
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range
import           System.IO.Unsafe

max_size :: Size
max_size = 32

hoistSupply :: (MFunctor t, Monad m) => r -> t (ReaderT r m) a -> t m a
hoistSupply r = hoist $ flip runReaderT r

-- TODO: make customizable.
genSizeDef :: Monad m => GenT m Size
genSizeDef = Gen.integral $ Range.linear 3 max_size

-- | The type used in generators defined in this module.
-- It is parameterized by an 'TheGenTypedBuiltin' which determines
-- how to generate sized builtins having a 'Size'. See for example
-- 'genTypedBuiltinSum' and 'genTypedBuiltinDiv'.
type GenPlcT m = GenT (ReaderT (TheGenTypedBuiltinT m) m)

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

runPlcT :: Monad m => GenTypedBuiltinT m -> GenPlcT m a -> GenT m a
runPlcT genTbs = hoistSupply $ TheGenTypedBuiltin genTbs

iterAppValueToTermOf :: IterAppValue head arg r -> TermOf r
iterAppValueToTermOf (IterAppValue term _ (TypedBuiltinValue _ x)) = TermOf term x

-- | Generate a value out of a 'TypeScheme' and return it along with the corresponding PLC value.
genSchemedPair :: Monad m => TypeScheme Size a r -> GenPlcT m (TermOf a)
genSchemedPair (TypeSchemeBuiltin tb) = do
    TheGenTypedBuiltin genTb <- ask
    hoist lift $ genTb tb
genSchemedPair (TypeSchemeArrow _ _)  = error "Not implemented."
genSchemedPair (TypeSchemeAllSize _)  = error "Not implemented."

genIterAppValue
    :: forall head r m. Monad m
    => Denotation head Size r
    -> GenPlcT m (IterAppValue head (Term TyName Name ()) r)
genIterAppValue (Denotation object toTerm meta scheme) = Gen.just $ go scheme (toTerm object) id meta where
    go
        :: TypeScheme Size c r
        -> Term TyName Name ()
        -> ([Term TyName Name ()] -> [Term TyName Name ()])
        -> c
        -> GenPlcT m (Maybe (IterAppValue head (Term TyName Name ()) r))
    go (TypeSchemeBuiltin builtin) term args y = do  -- Computed the result.
        return $ case unsafePerformIO . tryAny $ evaluate y of
            Left _   -> Nothing
            Right y' -> do
                let pia = IterApp object $ args []
                    tbv = TypedBuiltinValue builtin y'
                return $ IterAppValue term pia tbv
    go (TypeSchemeArrow schA schB) term args f = do  -- Another argument is required.
        TermOf v x <- genSchemedPair schA            -- Get a Haskell and the correspoding PLC values.

        let term' = Apply () term v                  -- Apply the term to the PLC value.
            args' = args . (v :)                     -- Append the PLC value to the spine.
            y     = f x                              -- Apply the Haskell function to the generated argument.
        go schB term' args' y
    go (TypeSchemeAllSize schK)    term args f = do
        size <- genSizeDef                           -- Generate a size.
        let term' = TyInst () term $ TyInt () size   -- Instantiate the term with the generated size.
        go (schK size) term' args f                  -- Instantiate a size variable with the generated size.

genTerm :: GenTypedBuiltin
genTerm tb =
    Gen.recursive Gen.choice [genTypedBuiltinDef tb] $
        let desizedTb = mapSizeEntryTypedBuiltin (\_ -> SizeBound ()) tb in
            case DMap.lookup desizedTb (unContext typedBuiltinNames) of
                Nothing                    -> []
                Just (Compose denotations) -> map gen denotations where
                    gen (MemberDenotation denotation)
                        = fmap iterAppValueToTermOf
                        . hoistSupply (TheGenTypedBuiltin genTerm)
                        $ genIterAppValue denotation

blah :: IO ()
blah = do
    tx <- Gen.sample $ genTerm TypedBuiltinBool
    putStrLn $ prettyString tx
