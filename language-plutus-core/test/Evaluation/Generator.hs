{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE OverloadedStrings         #-}
module Evaluation.Generator
    ( max_size
    , genSizeDef
    , typedBuiltinAsValue
    , GenPlc
    , runPlc
    , PrimIterAppValue(..)
    , genTypedBuiltin
    , genPrimIterAppValue
    , genTypedBuiltinAndItsValue
    , genConstant
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Evaluation.Constant.GenTypedBuiltinSized

import           Control.Monad.Reader
import           Control.Monad.Morph
import           Data.Text.Prettyprint.Doc
import           Hedgehog hiding (Size, Var, annotate)
import qualified Hedgehog.Gen   as Gen
import qualified Hedgehog.Range as Range

max_size :: Size
max_size = 128

genSizeDef :: Monad m => GenT m Size
genSizeDef = Gen.integral $ Range.exponential 1 max_size

-- | Coerce a Haskell value to a PLC value checking all constraints
-- (e.g. an 'Integer' is in appropriate bounds) along the way and
-- fail in case constraints are not satisfied.
typedBuiltinAsValue :: Monad m => TypedBuiltin Size a -> a -> GenT m (Value TyName Name ())
typedBuiltinAsValue tb x = maybe (error err) return $ makeConstant tb x where
    sx = prettyString $ TypedBuiltinValue tb x
    err = "prop_typedAddInteger: out of bounds: " ++ sx

-- | The type used in generators defined in this module.
-- It is parameterized by an 'TheGenTypedBuiltinSized' which determines
-- how to generate sized builtins having a 'Size'. See for example
-- 'genTypedBuiltinSizedSum' and 'genTypedBuiltinSizedDiv'.
type GenPlc = GenT (Reader TheGenTypedBuiltinSized)

data PrimIterAppValue = forall a. PrimIterAppValue
    (Term TyName Name ())
    (PrimIterApp TyName Name ())
    (TypedBuiltinValue Size a)

instance Pretty PrimIterAppValue where
    pretty (PrimIterAppValue term pia tbv) = parens $ mconcat
        [ "As a term: ", pretty term, line
        , "As an iterated application: ", pretty pia, line
        , "As a value: ", pretty tbv
        ]

runPlc :: GenTypedBuiltinSized -> GenPlc a -> Gen a
runPlc genTbs = hoist $ flip runReaderT $ TheGenTypedBuiltinSized genTbs

-- | Generate a value of one of the builtin types.
-- See 'TypedBuiltin' for the list of such types.
genTypedBuiltin :: TypedBuiltin Size a -> GenPlc a
genTypedBuiltin (TypedBuiltinSized sizeEntry tbs) = do
    let size = flattenSizeEntry sizeEntry
    TheGenTypedBuiltinSized genTbs <- ask
    genTbs size tbs
genTypedBuiltin TypedBuiltinBool                  = Gen.bool

-- | Generate a value of one of the builtin types (see 'TypedBuiltin' for
-- the list of such types) and return it along with the corresponding PLC value.
genTypedBuiltinAndItsValue :: TypedBuiltin Size a -> GenPlc (a, Value TyName Name ())
genTypedBuiltinAndItsValue tb = do
    x <- genTypedBuiltin tb
    v <- typedBuiltinAsValue tb x
    return (x, v)

genSchemedAndItsValue :: TypeScheme Size a -> GenPlc (a, Value TyName Name ())
genSchemedAndItsValue (TypeSchemeBuiltin tb) = genTypedBuiltinAndItsValue tb
genSchemedAndItsValue (TypeSchemeArrow _ _)  = error "Not implemented."
genSchemedAndItsValue (TypeSchemeAllSize _)  = error "Not implemented."

genPrimIterAppValue
    :: TypedBuiltinName a       -- ^ A (typed) builtin name to apply.
    -> a                        -- ^ The semantics of the builtin name. E.g. the semantics of
                                -- 'AddInteger' (and hence 'typedAddInteger') is '(+)'.
    -> GenPlc PrimIterAppValue
genPrimIterAppValue (TypedBuiltinName name schema) op = go schema term0 id op where
    term0 = Constant () $ BuiltinName () name

    go
        :: TypeScheme Size a
        -> Term TyName Name ()
        -> ([Value TyName Name ()] -> [Value TyName Name ()])
        -> a
        -> GenPlc PrimIterAppValue
    go (TypeSchemeBuiltin builtin) term args y = do  -- Computed the result.
        let pia = IterApp name $ args []
            tbv = TypedBuiltinValue builtin y
        return $ PrimIterAppValue term pia tbv
    go (TypeSchemeArrow schA schB) term args f = do  -- Another argument is required.
        (x, v) <- genSchemedAndItsValue schA         -- Get a Haskell and the correspoding PLC values.
        let term' = Apply () term v                  -- Apply the term to the PLC value.
            args' = args . (v :)                     -- Add the PLC value to the spine.
            y     = f x                              -- Apply the Haskell function to the generated argument.
        go schB term' args' y
    go (TypeSchemeAllSize schK)    term args f = do
        size <- genSizeDef                           -- Generate a size.
        let term' = TyInst () term $ TyInt () size   -- Instantiate the term with the generated size.
        go (schK size) term' args f                  -- Instantiate a size variable with the generated size.

genConstant :: Size -> Gen (Constant ())
genConstant size = Gen.choice
    [ BuiltinInt () size <$> genTypedBuiltinSizedDef size TypedBuiltinSizedInt
    , BuiltinBS  () size <$> genTypedBuiltinSizedDef size TypedBuiltinSizedBS
    , return $ BuiltinSize () size
    ]
