{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module GeneratorSpec where

import PlutusCore.Generators.PIR

import Control.Monad.Reader

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set qualified as Set

import Data.Char
import Data.List hiding (insert)
import Data.List.NonEmpty (NonEmpty (..))
import Text.Printf

import PlutusCore.Default
import PlutusCore.Name
import PlutusCore.Quote (runQuoteT)
import PlutusCore.Rename
import PlutusIR
import PlutusIR.Core.Instance.Pretty.Readable

import Data.Maybe
import Data.String

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.QuickCheck

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
--   forAllDoc "_,tm" genTypeAndTermNoHelp_ (shrinkTypedTerm mempty mempty) $ \ (_, tm) ->
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
prop_genKindCorrect :: Property
prop_genKindCorrect =
  forAllDoc "ctx" genCtx (const []) $ \ ctx ->
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType ctx) $ \ (k, ty) ->
  checkKind ctx ty k

-- | Check that shrinking types maintains kinds
prop_shrinkTypeSound :: Property
prop_shrinkTypeSound =
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType Map.empty) $ \ (k, ty) ->
  -- See discussion about the same trick in `prop_shrinkTermSound`
  checkKind Map.empty ty k ==>
  checkNoCounterexamples [ (k, ty) | (k, ty) <- shrinkKindAndType Map.empty (k, ty)
                                   , not $ checkKind Map.empty ty k ]

-- | Test that our generators only result in well-typed terms.
prop_genTypeCorrect :: Property
prop_genTypeCorrect =
  forAllDoc "ty,tm" genTypeAndTerm_ (const []) $ \ (ty, tm) -> typeCheckTerm tm ty

-- | Test that when we generate a fully applied term we end up
-- with a well-typed term.
prop_genWellTypedFullyApplied :: Property
prop_genWellTypedFullyApplied =
  forAllDoc "ty, tm" genTypeAndTerm_ (shrinkTypedTerm mempty mempty) $ \ (ty, tm) ->
  forAllDoc "ty', tm'" (genFullyApplied ty tm) (const []) $ \ (ty', tm') -> typeCheckTerm tm' ty'

-- | Test that shrinking a well-typed term results in a well-typed term
prop_shrinkTermSound :: Property
prop_shrinkTermSound =
  forAllShrinkBlind (pure False) (\ sh -> [ True | not sh ]) $ \ _ ->
  forAllDoc "ty,tm"   genTypeAndTerm_ shrinkClosedTypedTerm $ \ (ty, tm) ->
  let shrinks = shrinkClosedTypedTerm (ty, tm) in
  -- While we generate well-typed terms we still need this check here for
  -- shrinking counterexamples to *this* property. If we find a term whose
  -- shrinks aren't well-typed we want to find smaller *well-typed* terms
  -- whose shrinks aren't well typed.
  typeCheckTerm tm ty ==>
  not (null shrinks) ==>
  checkNoCounterexamples [ (ty, tm, scopeCheckTyVars Map.empty (ty, tm))
                         | (ty, tm) <- shrinks, not $ typeCheckTerm tm ty ]

-- * Utility tests for debugging generators that behave weirdly

-- | Test that `typeInstTerm` results in a well-typed instantiation.
prop_typeInstTerm :: Property
prop_typeInstTerm =
  forAllDoc "ctx"    genCtx                      (const [])       $ \ ctx ->
  forAllDoc "ty"     (genTypeWithCtx ctx $ Star) (shrinkType ctx) $ \ ty ->
  forAllDoc "target" (genTypeWithCtx ctx $ Star) (shrinkType ctx) $ \ target ->
  doTypeInstTermCheck ctx ty target
  where
    doTypeInstTermCheck :: Map TyName (Kind ())
                        -> Type TyName DefaultUni ()
                        -> Type TyName DefaultUni ()
                        -> Property
    doTypeInstTermCheck ctx ty target =
      case [ (n, insts)
           | n <- [0..arity ty+3]
           , Just insts <- [typeInstTerm ctx n target ty]
           , not $ checkInst ctx x ty insts target
           ] of
        []  -> property True
        bad -> ceDoc (prettyPirReadable bad) False
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
  forAllDoc "_,tm" genTypeAndTerm_ shrinkClosedTypedTerm $ \ (_, tm) ->
  tabulate "vars" (map (filter isAlpha . show . prettyPirReadable) $ vars tm) $ property True
  where
    vars (Var _ x)        = [x]
    vars (TyInst _ a _)   = vars a
    vars (Let _ _ _ b)    = vars b
    vars (LamAbs _ _ _ b) = vars b
    vars (Apply _ a b)    = vars a ++ vars b
    vars Error{}          = [Name "error" $ toEnum 0]
    vars _                = []

-- | Check the ratio of duplicate shrinks
prop_stats_numShrink :: Property
prop_stats_numShrink = forAllDoc "ty,tm" genTypeAndTerm_ (const []) $ \ (ty, tm) ->
  let shrinks = shrinkClosedTypedTerm (ty, tm)
      n = fromIntegral (length shrinks)
      u = fromIntegral (length $ nub shrinks)
      r | n > 0     = (n - u) / n :: Double
        | otherwise = 0
  in tabulate "r" [printf "%0.1f" r] True

-- | Specific test that `inhabitType` returns well-typed things
prop_inhabited :: Property
prop_inhabited =
  forAllDoc "ty,tm" (genInhab mempty) (shrinkTypedTerm mempty mempty) $ \ (ty, tm) -> typeCheckTerm tm ty
  where
    genInhab ctx = runGenTm $ local (\ e -> e { geTypes = ctx }) $
      genDatatypeLets $ \ dats -> do
        ty <- genType Star
        tm <- inhabitType ty
        return (ty, foldr (\ dat -> Let () NonRec (DatatypeBind () dat :| [])) tm dats)

-- | Test that shrinking types results in smaller types. Useful for debugging shrinking.
prop_shrinkTypeSmaller :: Property
prop_shrinkTypeSmaller =
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType Map.empty) $ \ (k, ty) ->
  checkNoCounterexamples [ (k', ty') | (k', ty') <- shrinkKindAndType Map.empty (k, ty), not $ leKind k' k ]

-- | Test that shrinking kinds generates smaller kinds
prop_shrinkKindSmaller :: Property
prop_shrinkKindSmaller =
  forAllDoc "k" arbitrary shrink $ \ k ->
  checkNoCounterexamples [ k' | k' <- shrink k, not $ ltKind k' k ]

-- | Test that fixKind actually gives you something of the right kind
prop_fixKind :: Property
prop_fixKind =
  forAllDoc "k,ty" genKindAndType (shrinkKindAndType Map.empty) $ \ (k, ty) ->
  checkNoCounterexamples [ (ty', k') | k' <- shrink k
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
  letCE "rename ty" (either undefined id . runQuoteT $ rename ty) $ \ rnty ->
  isJust $ unifyType mempty mempty mempty ty rnty

-- | Check that substitution gets rid of all the right variables
prop_substType :: Property
prop_substType =
  forAllDoc "ctx" genCtx (const []) $ \ ctx ->
  forAllDoc "ty" (genTypeWithCtx ctx Star) (shrinkType ctx) $ \ ty ->
  forAllDoc "sub" (genSubst ctx) (shrinkSubst ctx) $ \ sub ->
  letCE "res" (substType sub ty) $ \ res ->
  fvTypeR sub ty == fvType res && checkKind ctx res Star
