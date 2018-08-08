{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE OverloadedStrings         #-}
module Evaluation.Generator
    ( GenPlcT
    , IterAppValue(..)
    , max_size
    , hoistSupply
    , genSizeDef
    , runPlcT
    , genIterAppValue
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Evaluation.Constant.GenTypedBuiltin

import           Control.Monad.Reader
import           Control.Monad.Morph
import           Data.Text.Prettyprint.Doc
import           Data.GADT.Compare
import           Data.Dependent.Map
import qualified Data.Dependent.Map as DMap
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range

max_size :: Size
max_size = 128

hoistSupply :: (MFunctor t, Monad m) => r -> t (ReaderT r m) a -> t m a
hoistSupply r = hoist $ flip runReaderT r

genSizeDef :: Monad m => GenT m Size
genSizeDef = Gen.integral $ Range.exponential 1 max_size

-- | The type used in generators defined in this module.
-- It is parameterized by an 'TheGenTypedBuiltin' which determines
-- how to generate sized builtins having a 'Size'. See for example
-- 'genTypedBuiltinSum' and 'genTypedBuiltinDiv'.
type GenPlcT m = GenT (ReaderT (TheGenTypedBuiltinT m) m)

data IterAppValue head arg r = IterAppValue
    (Term TyName Name ())
    (IterApp head arg)
    (TypedBuiltinValue Size r)

instance (Pretty head, Pretty arg) => Pretty (IterAppValue head arg r) where
    pretty (IterAppValue term pia tbv) = parens $ mconcat
        [ "{ As a term: ", pretty term, line
        , "| As an iterated application: ", pretty pia, line
        , "| As a value: ", pretty tbv, line
        , "}"
        ]

runPlcT :: Monad m => GenTypedBuiltinT m -> GenPlcT m a -> GenT m a
runPlcT genTbs = hoistSupply $ TheGenTypedBuiltin genTbs

-- | Generate a value out of a 'TypeScheme' and return it along with the corresponding PLC value.
genSchemedPair :: Monad m => TypeScheme Size a r -> GenPlcT m (TermOf a)
genSchemedPair (TypeSchemeBuiltin tb) = do
    TheGenTypedBuiltin genTb <- ask
    hoist lift $ genTb tb
genSchemedPair (TypeSchemeArrow _ _)  = error "Not implemented."
genSchemedPair (TypeSchemeAllSize _)  = error "Not implemented."

genIterAppValue
    :: forall head a r m. Monad m
    => (head -> Term TyName Name ())
    -> Typed head a r                 -- ^ A (typed) builtin name to apply.
    -> a                              -- ^ The semantics of the builtin name. E.g. the semantics of
                                      -- 'AddInteger' (and hence 'typedAddInteger') is '(+)'.
    -> GenPlcT m (IterAppValue head (Term TyName Name ()) r)
genIterAppValue embHead (Typed h schema) op = go schema (embHead h) id op where
    go
        :: TypeScheme Size c r
        -> Term TyName Name ()
        -> ([Term TyName Name ()] -> [Term TyName Name ()])
        -> c
        -> GenPlcT m (IterAppValue head (Term TyName Name ()) r)
    go (TypeSchemeBuiltin builtin) term args y = do  -- Computed the result.
        let pia = IterApp h $ args []
            tbv = TypedBuiltinValue builtin y
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



data SomeTypedSized v size r = forall a. SomeTypedSized
    { _someTypedSizedValue  :: v
    , _someTypedSizedScheme :: TypeScheme size a r
    }

newtype Context v size = Context
    { unContext :: DMap (TypedBuiltin (Maybe size)) (SomeTypedSized v size)
    }

instance GEq (TypedBuiltin size)
instance GCompare (TypedBuiltin size)

insertTypedBuiltinName :: Typed BuiltinName a r -> Context BuiltinName size -> Context BuiltinName size
insertTypedBuiltinName (Typed name scheme) (Context vs) =
    Context $ DMap.insert (typeSchemeResult scheme) (SomeTypedSized name scheme) vs

typedBuiltinNames :: Context BuiltinName size
typedBuiltinNames
    = insertTypedBuiltinName typedAddInteger
    $ Context DMap.empty

iterAppValueToTermOf :: IterAppValue head arg r -> TermOf r
iterAppValueToTermOf (IterAppValue term _ (TypedBuiltinValue _ x)) = TermOf term x

-- TypedBuiltin Size a -> GenT m (TermOf a)
genTerm :: GenTypedBuiltin
genTerm tb = Gen.recursive Gen.choice [genTypedBuiltinDef tb] . pure $ case tb of
    TypedBuiltinSized _ TypedBuiltinSizedInt ->
        iterAppValueToTermOf <$> hoistSupply (TheGenTypedBuiltin genTerm)
            (genIterAppValue (Constant () . BuiltinName ()) typedAddInteger (+))

-- { As a term: [ [ { (con addInteger) (con 2) } (con 2 ! -32633) ] (con 2 ! -23301) ]
-- | As a value: -55934
-- }
blah :: IO ()
blah = do
    tx <- Gen.sample $ genTerm (TypedBuiltinSized (SizeValue 4) TypedBuiltinSizedInt)
    putStrLn $ prettyString tx
