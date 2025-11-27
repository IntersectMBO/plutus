-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Generators of various PLC things: 'Builtin's, 'IterApp's, 'Term's, etc.
module PlutusCore.Generators.Hedgehog.Entity
  ( PlcGenT
  , IterApp (..)
  , IterAppValue (..)
  , runPlcT
  , withTypedBuiltinGen
  , genIterAppValue
  , genTerm
  , genTermLoose
  , withAnyTermLoose
  ) where

import PlutusPrelude

import PlutusCore.Generators.Hedgehog.Denotation
import PlutusCore.Generators.Hedgehog.TypedBuiltinGen
import PlutusCore.Generators.Hedgehog.Utils

import PlutusCore.Builtin
import PlutusCore.Core
import PlutusCore.Default
import PlutusCore.Name.Unique
import PlutusCore.Pretty (PrettyConst, botRenderContext, prettyConst)
import PlutusCore.Quote

import Control.Monad.Morph qualified as Morph
import Control.Monad.Reader
import Data.ByteString qualified as BS
import Data.Kind as GHC
import Data.Proxy
import Hedgehog hiding (Size, Var)
import Hedgehog.Gen qualified as Gen
import Prettyprinter
import Type.Reflection

type Plain f (uni :: GHC.Type -> GHC.Type) (fun :: GHC.Type) = f TyName Name uni fun ()

-- | Generators of built-ins supplied to computations that run in the 'PlcGenT' monad.
newtype BuiltinGensT uni fun m = BuiltinGensT
  { _builtinGensTyped :: TypedBuiltinGenT (Plain Term uni fun) m
  {-^ Generates a PLC 'Term' and the corresponding
  Haskell value out of a 'TypedBuiltin'. -}
  }

{-| The type used in generators defined in this module.
It's parameterized by a 'BuiltinGensT' which makes it possible to supply
different generators of built-in types. For example, 'genTypedBuiltinDiv'
never generates a zero, so this generator can be used in order to avoid the
divide-by-zero-induced @error@. Supplied generators are of arbitrary complexity
and can call the currently running generator recursively, for example. -}
type PlcGenT uni fun m = GenT (ReaderT (BuiltinGensT uni fun m) m)

-- | A function (called "head") applied to a list of arguments (called "spine").
data IterApp head arg = IterApp
  { _iterAppHead :: head
  , _iterAppSpine :: [arg]
  }

instance (PrettyBy config head, PrettyBy config arg) => PrettyBy config (IterApp head arg) where
  prettyBy config (IterApp appHead appSpine) =
    parens $ foldl' (\fun arg -> fun <+> prettyBy config arg) (prettyBy config appHead) appSpine

-- | One iterated application of a @head@ to @arg@s represented in three distinct ways.
data IterAppValue uni fun head arg r = IterAppValue
  { _iterTerm :: Plain Term uni fun
  -- ^ As a PLC 'Term'.
  , _iterApp :: IterApp head arg
  -- ^ As an 'IterApp'.
  , _iterTbv :: r
  -- ^ As a Haskell value.
  }

instance
  ( PrettyBy config (Plain Term uni fun)
  , PrettyBy config head
  , PrettyBy config arg
  , PrettyConst r
  )
  => PrettyBy config (IterAppValue uni fun head arg r)
  where
  prettyBy config (IterAppValue term pia y) =
    parens $
      fold
        [ "{ "
        , prettyBy config term
        , line
        , "| "
        , prettyBy config pia
        , line
        , "| "
        , prettyConst botRenderContext y
        , line
        , "}"
        ]

-- | Run a 'PlcGenT' computation by supplying built-ins generators.
runPlcT :: Monad m => TypedBuiltinGenT (Plain Term uni fun) m -> PlcGenT uni fun m a -> GenT m a
runPlcT genTb = hoistSupply $ BuiltinGensT genTb

-- | Get a 'TermOf' out of an 'IterAppValue'.
iterAppValueToTermOf :: IterAppValue uni fun head arg r -> TermOf (Plain Term uni fun) r
iterAppValueToTermOf (IterAppValue term _ y) = TermOf term y

{-| Add to the 'ByteString' representation of a 'Name' its 'Unique'
without any additional symbols inbetween. -}
revealUnique :: Name -> Name
revealUnique (Name name uniq) =
  Name (name <> display (unUnique uniq)) uniq

-- TODO: we can generate more types here.
-- | Generate a 'Builtin' and supply its typed version to a continuation.
withTypedBuiltinGen
  :: Monad m
  => Proxy fun
  -> ( forall a
        . (KnownTypeAst TyName DefaultUni a, MakeKnown (Plain Term DefaultUni fun) a)
       => TypeRep a -> GenT m c
     )
  -> GenT m c
withTypedBuiltinGen _ k =
  Gen.choice
    [ k @Integer typeRep
    , k @BS.ByteString typeRep
    , k @Bool typeRep
    ]

{-| Generate an 'IterAppValue' from a 'Denotation'.
If the 'Denotation' has a functional type, then all arguments are generated and
supplied to the denotation. Since 'IterAppValue' consists of three components, we
  1. grow the 'Term' component by applying it to arguments using 'Apply'
  2. grow the 'IterApp' component by appending arguments to its spine
  3. feed arguments to the Haskell function -}
genIterAppValue
  :: forall head uni fun res m
   . Monad m
  => Denotation (Plain Term uni fun) head res
  -> PlcGenT uni fun m (IterAppValue uni fun head (Plain Term uni fun) res)
genIterAppValue (Denotation object embed meta scheme) = result
  where
    result = go scheme (embed object) id meta

    go
      :: TypeScheme (Plain Term uni fun) args res
      -> Plain Term uni fun
      -> ([Plain Term uni fun] -> [Plain Term uni fun])
      -> FoldArgs args res
      -> PlcGenT uni fun m (IterAppValue uni fun head (Plain Term uni fun) res)
    go TypeSchemeResult term args y = do
      -- Computed the result.
      let pia = IterApp object $ args []
      return $ IterAppValue term pia y
    go (TypeSchemeArrow schB) term args f = do
      -- Another argument is required.
      BuiltinGensT genTb <- ask
      TermOf v x <- liftT $ genTb typeRep -- Get a Haskell and the corresponding PLC values.
      let term' = Apply () term v -- Apply the term to the PLC value.
          args' = args . (v :) -- Append the PLC value to the spine.
          y = f x -- Apply the Haskell function to the generated argument.
      go schB term' args' y
    go (TypeSchemeAll _ schK) term args f =
      go schK term args f

{-| Generate a PLC 'Term' of the specified type and the corresponding Haskell value.
Generates first-order functions and constants including constant applications.
Arguments to functions and 'Builtin's are generated recursively. -}
genTerm
  :: forall uni fun m
   . (uni ~ DefaultUni, Monad m)
  => TypedBuiltinGenT (Plain Term uni fun) m
  -- ^ Ground generators of built-ins. The base case of the recursion.
  -> DenotationContext (Plain Term uni fun)
  {-^ A context to generate terms in. See for example 'typedBuiltins'.
  Gets extended by a variable when an applied lambda is generated. -}
  -> Int
  -- ^ Depth of recursion.
  -> TypedBuiltinGenT (Plain Term uni fun) m
genTerm genBase context0 depth0 = Morph.hoist runQuoteT . go context0 depth0
  where
    go
      :: DenotationContext (Plain Term uni fun)
      -> Int
      -> TypeRep r
      -> GenT (QuoteT m) (TermOf (Plain Term uni fun) r)
    go context depth tr
      -- FIXME: should be using 'variables' but this is now the same as 'recursive'
      | depth == 0 = choiceDef (liftT $ genBase tr) []
      | depth == 1 = choiceDef (liftT $ genBase tr) $ variables ++ recursive
      | depth == 2 = Gen.frequency $ stopOrDeeper ++ map (3,) variables ++ map (5,) recursive
      | depth == 3 = Gen.frequency $ stopOrDeeper ++ map (3,) recursive
      | otherwise = Gen.frequency stopOrDeeper
      where
        stopOrDeeper = [(1, liftT $ genBase tr), (5, lambdaApply)]
        -- Generators of built-ins to feed them to 'genIterAppValue'.
        -- Note that the typed built-ins generator calls 'go' recursively.
        builtinGens = BuiltinGensT (flip Gen.subterm id . go context (depth - 1))
        -- Generate arguments for functions recursively or return a variable.
        proceed (DenotationContextMember denotation) =
          fmap iterAppValueToTermOf . hoistSupply builtinGens $ genIterAppValue denotation
        -- A list of variables generators.
        variables = map proceed $ lookupInContext tr context
        -- A list of recursive generators.
        recursive = map proceed $ lookupInContext tr context
        -- Generate a lambda and immediately apply it to a generated argument of a generated type.
        lambdaApply = withTypedBuiltinGen (Proxy @fun) $ \argTr -> do
          -- Generate a name for the name representing the argument.
          name <- lift $ revealUnique <$> freshName "x"
          -- Get the 'Type' of the argument from a generated 'TypedBuiltin'.
          let argTy = toTypeAst argTr
          -- Generate the argument.
          TermOf arg x <- go context (depth - 1) argTr
          -- Generate the body of the lambda abstraction adding the new variable to the context.
          TermOf body y <- go (insertVariable name argTr x context) (depth - 1) tr
          -- Assemble the term.
          let term = Apply () (LamAbs () name argTy body) arg
          return $ TermOf term y

{-| Generates a 'Term' with rather small values to make out-of-bounds failures less likely.
There are still like a half of terms that fail with out-of-bounds errors being evaluated. -}
genTermLoose :: Monad m => TypedBuiltinGenT (Plain Term DefaultUni DefaultFun) m
genTermLoose = genTerm genTypedBuiltinDef typedBuiltins 4

{-| Generate a 'TypedBuiltin' and a 'TermOf' of the corresponding type,
attach the 'TypedBuiltin' to the value part of the 'TermOf' and pass that to a continuation. -}
withAnyTermLoose
  :: (uni ~ DefaultUni, fun ~ DefaultFun, Monad m)
  => (forall a. KnownType (Plain Term uni fun) a => TermOf (Plain Term uni fun) a -> GenT m c)
  -> GenT m c
withAnyTermLoose k = withTypedBuiltinGen (Proxy @DefaultFun) $ \tr -> genTermLoose tr >>= k
