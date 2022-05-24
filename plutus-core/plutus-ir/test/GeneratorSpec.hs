{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module GeneratorSpec where

import PlutusCore.Generators.PIR

import Control.Monad.Reader

import Data.Map qualified as Map
import Data.Set qualified as Set

import Data.Char
import Data.List hiding (insert)
import Data.List.NonEmpty (NonEmpty (..))
import Text.Printf

import PlutusCore.Name
import PlutusCore.Quote (runQuote)
import PlutusCore.Rename
import PlutusIR
import PlutusIR.Core.Instance.Pretty.Readable

import Data.Maybe
import Data.String

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.QuickCheck

-- | Check that a list of potential counterexamples is empty and display the
-- list as a QuickCheck counterexample if its not.
assertNoCounterexamples :: PrettyPir a => [a] -> Property
assertNoCounterexamples []  = property True
assertNoCounterexamples bad = ceDoc (prettyPirReadable bad) False

-- CODE REVIEW: The property below checks that when we run a generated PIR term through the compiler
-- we actually get something out. As the generators are supposed to generate reasonable stuff this is
-- a test of the compiler. I think we
--  1. Want this somewhere
--  2. Don't want it here
--  Where do we want something like this?
--  Also, the code below is a giant hack to "conenct to" the compiler at the "right" place (as judged
--  by us when we were ripping the compiler apart to extract something that did something reasonable-ish)
--
-- TODO: we want this property somewhere!
-- compile :: Term TyName Name DefaultUni DefaultFun ()
--         -> Either (CompileError DefaultUni DefaultFun) (CompiledCode a)
-- compile _tm = either Left Right $ runQuoteT $ do
--   -- Make sure that names are unique (that's not guaranteed by QuickCheck)
--   tm <- rename _tm
--   plcTcConfig <- PLC.getDefTypeCheckConfig PIR.noProvenance
--   let hints = UPLC.InlineHints $ \a _ -> case a of
--                 PIR.DatatypeComponent PIR.Destructor _ -> True
--                 _                                      -> False
--       pirCtx = PIR.toDefaultCompilationCtx plcTcConfig
--              & set (PIR.ccOpts . PIR.coOptimize) True
--              & set (PIR.ccOpts . PIR.coPedantic) False
--              & set (PIR.ccOpts . PIR.coVerbose) False
--              & set (PIR.ccOpts . PIR.coDebug) False
--              & set (PIR.ccOpts . PIR.coMaxSimplifierIterations)
--                       (PIR.defaultCompilationOpts ^. PIR.coMaxSimplifierIterations)
--              & set PIR.ccTypeCheckConfig Nothing
--       uplcSimplOpts = UPLC.defaultSimplifyOpts
--             & set UPLC.soMaxSimplifierIterations (PIR.defaultCompilationOpts ^. PIR.coMaxSimplifierIterations)
--             & set UPLC.soInlineHints hints
--
--   plcT <- flip runReaderT pirCtx $ PIR.compileReadableToPlc $ fmap Original tm
--   plcTcError <- runExceptT @(PLC.Error _ _ _)
--              $ UPLC.deBruijnTerm =<< UPLC.simplifyTerm uplcSimplOpts (UPLC.erase plcT)
--   case plcTcError of
--     Left _   -> error "wrong"
--     Right cc -> return $ DeserializedCode (UPLC.Program () (PLC.defaultVersion ()) $ void cc) Nothing mempty
--
-- prop_compile :: Property
-- prop_compile =
--   forAllDoc "_,tm" genTypeAndTermNoHelp_ shrinkClosedTypedTerm $ \ (_, tm) ->
--   isRight $ compile tm

generators :: TestNested
generators = return $ testGroup "generators"
  [ testProperty "prop_genKindCorrect"  $ withMaxSuccess 1000 prop_genKindCorrect
  , testProperty "prop_shrinkTypeSound" $ prop_shrinkTypeSound
  , testProperty "prop_genTypeCorrect"  $ withMaxSuccess 1000 prop_genTypeCorrect
  , testProperty "prop_shrinkTermSound" $ withMaxSuccess 20 prop_shrinkTermSound
  ]

-- * Core properties for PIR generators

-- | Check that the types we generate are kind-correct
-- See Note [Debugging generators that don't generate well-typed/kinded terms/types]
-- when this property fails.
prop_genKindCorrect :: Property
prop_genKindCorrect =
  -- Context minimality doesn't help readability, so no shrinking here
  forAllDoc "ctx" genCtx (const []) $ \ ctx ->
  -- Note, no shrinking here because shrinking relies on well-kindedness.
  forAllDoc "k,ty" genKindAndType (const []) $ \ (k, ty) ->
  checkKind ctx ty k

-- | Check that shrinking types maintains kinds
prop_shrinkTypeSound :: Property
prop_shrinkTypeSound =
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType Map.empty) $ \ (k, ty) ->
  -- See discussion about the same trick in `prop_shrinkTermSound`
  checkKind Map.empty ty k ==>
  assertNoCounterexamples [ (k, ty) | (k, ty) <- shrinkKindAndType Map.empty (k, ty)
                                   , not $ checkKind Map.empty ty k ]

-- | Test that our generators only result in well-typed terms.
-- Note, the counterexamples from this property are not shrunk (see why below).
-- See Note [Debugging generators that don't generate well-typed/kinded terms/types]
-- when this property fails.
prop_genTypeCorrect :: Property
prop_genTypeCorrect =
  -- Note, we don't shrink this term here because a precondition of shrinking is that
  -- the term we are shrinking is well-typed. If it is not, the counterexample we get
  -- from shrinking will be nonsene.
  forAllDoc "ty,tm" genTypeAndTerm_ (const []) $ \ (ty, tm) -> typeCheckTerm tm ty

-- | Test that when we generate a fully applied term we end up
-- with a well-typed term.
prop_genWellTypedFullyApplied :: Property
prop_genWellTypedFullyApplied =
  forAllDoc "ty, tm" genTypeAndTerm_ shrinkClosedTypedTerm $ \ (ty, tm) ->
  -- No shrinking here because if `genFullyApplied` is wrong then the shrinking
  -- will be wrong too. See `prop_genTypeCorrect`.
  forAllDoc "ty', tm'" (genFullyApplied ty tm) (const []) $ \ (ty', tm') ->
  typeCheckTerm tm' ty'

-- | Test that shrinking a well-typed term results in a well-typed term
prop_shrinkTermSound :: Property
prop_shrinkTermSound =
  forAllDoc "ty,tm"   genTypeAndTerm_ shrinkClosedTypedTerm $ \ (ty, tm) ->
  let shrinks = shrinkClosedTypedTerm (ty, tm) in
  -- While we generate well-typed terms we still need this check here for
  -- shrinking counterexamples to *this* property. If we find a term whose
  -- shrinks aren't well-typed we want to find smaller *well-typed* terms
  -- whose shrinks aren't well typed.
  -- Importantly, this property is only interesting when
  -- shrinking itself is broken, so we can only use the
  -- parts of shrinking that happen to be OK.
  typeCheckTerm tm ty ==>
  -- We don't want to let the shrinker get away with being empty, so we ignore empty shrinks. QuickCheck will give
  -- up and print an error if the shrinker returns the empty list too often.
  not (null shrinks) ==>
  assertNoCounterexamples [ (ty, tm, scopeCheckTyVars Map.empty (ty, tm))
                         | (ty, tm) <- shrinks, not $ typeCheckTerm tm ty ]

-- * Utility tests for debugging generators that behave weirdly

-- | Test that `typeInstTerm` results in a well-typed instantiation.
prop_typeInstTerm :: Property
prop_typeInstTerm =
  forAllDoc "ctx"    genCtx                      (const [])       $ \ ctx ->
  forAllDoc "ty"     (genTypeWithCtx ctx $ Star) (shrinkType ctx) $ \ ty ->
  forAllDoc "target" (genTypeWithCtx ctx $ Star) (shrinkType ctx) $ \ target ->
  assertNoCounterexamples [ (n, insts)
                         | n <- [0..arity ty+3]
                         , Just insts <- [typeInstTerm ctx n target ty]
                         , not $ checkInst ctx x ty insts target
                         ]
  where
    x = Name "x" (toEnum 0)
    arity (TyForall _ _ _ a) = arity a
    arity (TyFun _ _ b)      = 1 + arity b
    arity _                  = 0

    checkInst ctx x ty insts target = typeCheckTermInContext ctx tmCtx tm target
      where
        (tmCtx, tm) = go (toEnum 1) (Map.singleton x ty) (Var () x) insts
        go _ tmCtx tm [] = (tmCtx, tm)
        go i tmCtx tm (InstApp ty : insts) = go i tmCtx (TyInst () tm ty) insts
        go i tmCtx tm (InstArg ty : insts) = go (succ i) (Map.insert y ty tmCtx)
                                                         (Apply () tm (Var () y)) insts
          where y = Name "y" i

-- | Check what's in the leaves of the generated data
prop_stats_leaves :: Property
prop_stats_leaves =
  -- No shrinking here because we are only collecting stats
  forAllDoc "_,tm" genTypeAndTerm_ (const []) $ \ (_, tm) ->
  tabulate "leaves" (map (filter isAlpha . show . prettyPirReadable) $ leaves tm) $ property True
  where
    -- Figure out what's at the leaves of the AST,
    -- including variable names, error, and builtins.
    leaves (Var _ x)        = [x]
    leaves (TyInst _ a _)   = leaves a
    leaves (Let _ _ _ b)    = leaves b
    leaves (LamAbs _ _ _ b) = leaves b
    leaves (Apply _ a b)    = leaves a ++ leaves b
    leaves Error{}          = [Name "error" $ toEnum 0]
    leaves Builtin{}        = [Name "builtin" $ toEnum 0]
    leaves _                = []

-- | Check the ratio of duplicate shrinks
prop_stats_numShrink :: Property
prop_stats_numShrink =
  -- No shrinking here because we are only collecting stats
  forAllDoc "ty,tm" genTypeAndTerm_ (const []) $ \ (ty, tm) ->
  let shrinks = shrinkClosedTypedTerm (ty, tm)
      n = fromIntegral (length shrinks)
      u = fromIntegral (length $ nub shrinks)
      r | n > 0     = (n - u) / n :: Double
        | otherwise = 0
  in tabulate "r" [printf "%0.1f" r] True

-- | Specific test that `inhabitType` returns well-typed things
prop_inhabited :: Property
prop_inhabited =
  -- No shrinking here because if the generator
  -- generates nonsense shrinking will be nonsense.
  forAllDoc "ty,tm" (genInhab mempty) (const []) $ \ (ty, tm) -> typeCheckTerm tm ty
  where
    -- Generate some datatypes and then immediately call
    -- `inhabitType` to test `inhabitType` directly instead
    -- of through the whole term generator. Quick-ish way
    -- of debugging "clever hacks" in `inhabitType`.
    genInhab ctx = runGenTm $ local (\ e -> e { geTypes = ctx }) $
      genDatatypeLets $ \ dats -> do
        ty <- genType Star
        tm <- inhabitType ty
        return (ty, foldr (\ dat -> Let () NonRec (DatatypeBind () dat :| [])) tm dats)

-- | Test that shrinking types results in smaller types. Useful for debugging shrinking.
prop_shrinkTypeSmallerKind :: Property
prop_shrinkTypeSmallerKind =
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType Map.empty) $ \ (k, ty) ->
  assertNoCounterexamples [ (k', ty')
                          | (k', ty') <- shrinkKindAndType Map.empty (k, ty)
                          , not $ leKind k' k ]

-- | Test that shrinking kinds generates smaller kinds
prop_shrinkKindSmaller :: Property
prop_shrinkKindSmaller =
  forAllDoc "k" arbitrary shrink $ \ k ->
  assertNoCounterexamples [ k' | k' <- shrink k, not $ leKind k' k ]

-- | Test that fixKind actually gives you something of the right kind
prop_fixKind :: Property
prop_fixKind =
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType Map.empty) $ \ (k, ty) ->
  -- Note, fixKind only works on smaller kinds, so we use shrink to get a definitely smaller kind
  assertNoCounterexamples [ (ty', k') | k' <- shrink k
                                     , let ty' = fixKind Map.empty ty k'
                                     , not $ checkKind Map.empty ty' k' ]

-- * Tests for unification and substitution

-- | Check that unification does the right thing.
prop_unify :: Property
prop_unify =
  forAllDoc "n"   arbitrary shrink         $ \ (NonNegative n) ->
  forAllDoc "m"   (choose (0, n)) shrink   $ \ m ->
  letCE "xs" (take n allTheVarsCalledX)    $ \ xs ->
  forAllDoc "ks"
    (vectorOf n arbitrary)
    (filter ((== n) . length) . shrink)    $ \ ks ->
  letCE "ctx" (Map.fromList                $ zip xs ks) $ \ ctx ->
  forAllDoc "ty1"
    (genTypeWithCtx ctx $ Star)
    (shrinkType ctx)                       $ \ ty1 ->
  forAllDoc "ty2"
    (genTypeWithCtx ctx $ Star)
    (shrinkType ctx)                       $ \ ty2 ->
  letCE "nty1" (normalizeTy ty1)           $ \ _ ->
  letCE "nty2" (normalizeTy ty2)           $ \ _ ->
  letCE "res" (unifyType ctx (Set.fromList $ take m xs) Map.empty ty1 ty2) $ \ res ->
  isJust res ==>
  let sub = fromJust res
      checkSub (x, ty) = letCE "x,ty" (x, ty)    $ \ _ ->
                         letCE "k" (ctx Map.! x) $ \ k -> checkKind ctx ty k
  in
  letCE "sty1" (substType sub ty1) $ \ sty1 ->
  letCE "sty2" (substType sub ty2) $ \ sty2 ->
  letCE "nsty1" (normalizeTy sty1) $ \ nsty1 ->
  letCE "nsty2" (normalizeTy sty2) $ \ nsty2 ->
  tabulate "sizes" [show $ min (Set.size $ fvType ty1) (Set.size $ fvType ty2)] $
  foldr (.&&.) (property $ nsty1 == nsty2) (map checkSub (Map.toList sub))
  where
    allTheVarsCalledX = [ TyName $ Name (fromString $ "x" ++ show i) (toEnum i) | i <- [1..] ]

-- | Check that a type unifies with a renaming of itself
prop_unifyRename :: Property
prop_unifyRename =
  forAllDoc "_, ty" genKindAndType (shrinkKindAndType mempty) $ \ (_, ty) ->
  letCE "rename ty" (runQuote $ rename ty) $ \ rnty ->
  isJust $ unifyType mempty mempty mempty ty rnty

-- | Check that substitution gets rid of all the right variables
prop_substType :: Property
prop_substType =
  -- No shrinking because every nested shrink makes properties
  -- harder to shrink and context minimality doesn't help readability very much.
  forAllDoc "ctx" genCtx (const []) $ \ ctx ->
  forAllDoc "ty" (genTypeWithCtx ctx Star) (shrinkType ctx) $ \ ty ->
  forAllDoc "sub" (genSubst ctx) (shrinkSubst ctx) $ \ sub ->
  letCE "res" (substType sub ty) $ \ res ->
  fvTypeR sub ty == fvType res && checkKind ctx res Star

-- | Check that there are no one-step shrink loops
prop_noTermShrinkLoops :: Property
prop_noTermShrinkLoops =
  -- Note that we need to remove x from the shrinks of x here because
  -- a counterexample to this property is otherwise guaranteed to
  -- go into a shrink loop.
  forAllDoc "ty,tm" genTypeAndTerm_ (\x -> filter (/= x) $ shrinkClosedTypedTerm x) $ \ tytm ->
  tytm `notElem` shrinkClosedTypedTerm tytm
