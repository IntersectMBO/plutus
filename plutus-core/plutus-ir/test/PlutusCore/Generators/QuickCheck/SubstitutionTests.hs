-- editorconfig-checker-disable-file
module PlutusCore.Generators.QuickCheck.SubstitutionTests where

import PlutusCore.Generators.QuickCheck

import PlutusCore.Name.Unique
import PlutusCore.Quote (runQuote)
import PlutusCore.Rename
import PlutusIR.Subst

import Control.Monad
import Data.Either
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import Data.String

import Test.QuickCheck hiding (choose, vectorOf)

-- * Tests for unification and substitution

{-| Check that unification does the right thing by

1. generating a context, substitution and two arbitrary types
2. checking that successful unification implies that each type in the resulting substitution has
the same kind as the variable it can be substituted for
3. checking that using the substitution on both the original types and normalizing the results
gives equal types

Two arbitrary types are not very likely to be unifiable, so we're throwing away quite a lot.
The statistics at the time this comment was written are as follows:

1. 85% of generated test cases get thrown away
2. of the remaining 15%:
2.1 85% are cases with one of the normalized types having only one type variable
2.2 10% are cases with one of the normalized types not having any type variables at all

So we don't get great coverage, but given that it takes a few seconds to generate dozens of
thousands of (non-filtered) test cases, we do still get some reasonable coverage in the end. -}
prop_unify :: Property
prop_unify = withMaxSuccess 500 $
  forAllDoc "n" arbitrary shrink $ \(NonNegative n) ->
    forAllDoc "nSub" (choose (0, n)) shrink $ \nSub ->
      -- See Note [Chaotic Good fresh name generation].
      let xVars = [TyName $ Name (fromString $ "x" ++ show i) (toEnum i) | i <- [1 .. n]]
       in -- Just for displaying @xVars@ in case of error.
          letCE "xVars" xVars $ \_ ->
            forAllDoc
              "kinds"
              (vectorOf n arbitrary)
              (filter ((== n) . length) . shrink)
              $ \kinds ->
                letCE "ctx" (Map.fromList $ zip xVars kinds) $ \ctx ->
                  forAllDoc
                    "ty1"
                    (genKindAndTypeWithCtx ctx)
                    (shrinkKindAndType ctx)
                    $ \(_, ty1) ->
                      forAllDoc
                        "ty2"
                        (genKindAndTypeWithCtx ctx)
                        (shrinkKindAndType ctx)
                        $ \(_, ty2) ->
                          letCE "nty1" (normalizeTy ty1) $ \nty1 ->
                            letCE "nty2" (normalizeTy ty2) $ \nty2 ->
                              letCE "res" (unifyType ctx (Set.fromList $ take nSub xVars) ty1 ty2) $ \res ->
                                isRight res ==>
                                  let sub = fromRight (error "impossible") res
                                      checkSub (x, ty) =
                                        letCE "x,ty" (x, ty) $ \_ ->
                                          letCE "k" (Map.findWithDefault (error "impossible") x ctx) $ \k ->
                                            checkKind ctx ty k
                                   in letCE "sty1" (substType sub ty1) $ \sty1 ->
                                        letCE "sty2" (substType sub ty2) $ \sty2 ->
                                          letCE "nsty1" (normalizeTy sty1) $ \nsty1 ->
                                            letCE "nsty2" (normalizeTy sty2) $ \nsty2 ->
                                              -- Since unification normalizes both the sides beforehand, we're displaying free variables of
                                              -- normalized types here.
                                              tabulate "sizes" [show $ min (Set.size $ setOf ftvTy nty1) (Set.size $ setOf ftvTy nty2)] $
                                                foldr (.&&.) (property $ nsty1 == nsty2) (map checkSub (Map.toList sub))

-- | Check that a type unifies with a renaming of itself
prop_unifyRename :: Property
prop_unifyRename =
  forAllDoc "_, ty" genKindAndType (shrinkKindAndType mempty) $ \(_, ty) ->
    letCE "rename ty" (runQuote $ rename ty) $ \rnty ->
      void $ unifyType mempty mempty ty rnty

{-| Check that substitution eliminates from the type all free occurrences of variables present in
the domain of the substitution. -}
prop_substType :: Property
prop_substType = withMaxSuccess 1000 $
  -- No shrinking because every nested shrink makes properties harder to shrink (because you'd need
  -- to regenerate the stuff that depends on the context, meaning you don't have the same
  -- counterexample as you did before) and context minimality doesn't help readability very much.
  forAllDoc "ctx" genCtx (const []) $ \ctx ->
    forAllDoc "ty" (genKindAndTypeWithCtx ctx) (shrinkKindAndType ctx) $ \(k, ty) ->
      forAllDoc "sub" (genSubst ctx) (shrinkSubst ctx) $ \sub ->
        letCE "res" (substType sub ty) $ \res -> do
          let fv1 = fvTypeR sub ty
              fv2 = setOf ftvTy res
          unless (fv1 == fv2) . Left $
            concat
              [ "Type variables of the generated type given the generated substitution don't match "
              , "those of the resulting type after the substitution is applied: \n\n"
              , show fv1
              , "\n\n  vs \n\n"
              , show fv2
              ]
          checkKind ctx res k
