-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Names.Spec where

import PlutusCore.Test

import PlutusCore
import PlutusCore.Mark
import PlutusCore.Pretty
import PlutusCore.Rename.Internal

import PlutusCore.Generators.Hedgehog
import PlutusCore.Generators.Hedgehog.AST as AST
import PlutusCore.Generators.Hedgehog.Interesting

import GHC.Exts (fromString)
import Hedgehog hiding (Var)
import Hedgehog.Gen qualified as Gen
import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

prop_DeBruijn :: Gen (TermOf (Term TyName Name DefaultUni DefaultFun ()) a) -> Property
prop_DeBruijn gen = property . generalizeT $ do
    TermOf body _ <- forAllNoShowT gen
    let
        forward = deBruijnTerm
        backward
            :: Either FreeVariableError (Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun a)
            -> Either FreeVariableError (Term TyName Name DefaultUni DefaultFun a)
        backward e = e >>= (\t -> runQuoteT $ unDeBruijnTerm t)
    Hedgehog.tripping body forward backward

test_DeBruijnInteresting :: TestTree
test_DeBruijnInteresting =
    testGroup "de Bruijn transformation round-trip" $
        fromInterestingTermGens $ \name -> testPropertyNamed name (fromString name) . prop_DeBruijn

test_mangle :: TestTree
test_mangle = testPropertyNamed "equality does not survive mangling" "equality_mangling" . property $ do
    (term, termMangled) <- forAll . Gen.just . runAstGen $ do
        term <- AST.genTerm
        mayTermMang <- mangleNames term
        pure $ do
            termMang <- mayTermMang
            Just (term, termMang)
    Hedgehog.assert $ term /= termMangled && termMangled /= term

-- | Test equality of a program and its renamed version, given a renamer.
prop_equalityFor
    :: program ~ Program TyName Name DefaultUni DefaultFun ()
    => (program -> Quote program) -> Property
prop_equalityFor ren = property $ do
    prog <- forAllPretty $ runAstGen genProgram
    let progRen = runQuote $ ren prog
    Hedgehog.assert $ progRen == prog && prog == progRen

test_equalityRename :: TestTree
test_equalityRename =
    testPropertyNamed "equality survives renaming" "equality_renaming" $
        prop_equalityFor rename

test_equalityBrokenRename :: TestTree
test_equalityBrokenRename =
    testCase "equality does not survive wrong renaming" $
        checkFails . prop_equalityFor $ brokenRename markNonFreshProgram renameProgramM

test_equalityNoMarkRename :: TestTree
test_equalityNoMarkRename =
    testCase "equality does not survive renaming without marking" $
        checkFails . prop_equalityFor $ noMarkRename renameProgramM

test_alphaEquality :: TestTree
test_alphaEquality = testCase "alphaEquality" $ do
    let
        xName = Name "x" (Unique 0)
        yName = Name "y" (Unique 1)

        varX = Var () xName
        varY = Var () yName

        varType = TyVar () (TyName (Name "a" (Unique 2)))

        lamX = LamAbs () xName varType varX
        lamY = LamAbs () yName varType varY

        term0, term1 :: Term TyName Name DefaultUni DefaultFun ()

        -- [(lam x a x) x]
        term0 = Apply () lamX varX
        -- [(lam y a y) x]
        term1 = Apply () lamY varX

    term0 @?= term1

test_rebindShadowedVariable :: TestTree
test_rebindShadowedVariable = testCase "rebindShadowedVariable" $ do
    let xName = TyName (Name "x" (Unique 0))
        yName = TyName (Name "y" (Unique 1))
        zName = TyName (Name "z" (Unique 2))

        varX = TyVar () xName
        varY = TyVar () yName
        varZ = TyVar () zName

        typeKind = Type ()

        l1, r1, l2, r2 :: Type TyName DefaultUni ()

        -- (all x (type) (fun (all y (type) y) x))
        l1 = TyForall () xName typeKind (TyFun () (TyForall () yName typeKind varY) varX)
        -- (all x (type) (fun (all x (type) x) x))
        r1 = TyForall () xName typeKind (TyFun () (TyForall () xName typeKind varX) varX)

        -- (all x (type) (all x (type) (fun x x)))
        l2 = TyForall () xName typeKind (TyForall () xName typeKind (TyFun () varX varX))
        -- (all y (type) (all z (type) (fun y z)))
        r2 = TyForall () yName typeKind (TyForall () zName typeKind (TyFun () varY varZ))

        err = concat
            [ displayPlcDebug l2
            , " and "
            , displayPlcDebug r2
            , " are supposed not to be equal, but they are equal"
            ]

    l1 @?= r1
    assertBool err $ l2 /= r2

test_rebindCapturedVariable :: TestTree
test_rebindCapturedVariable = testCase "rebindCapturedVariable" $ do
    let wName = TyName (Name "w" (Unique 0))
        xName = TyName (Name "x" (Unique 1))
        yName = TyName (Name "y" (Unique 2))
        zName = TyName (Name "z" (Unique 3))

        varW = TyVar () wName
        varX = TyVar () xName
        varY = TyVar () yName
        varZ = TyVar () zName

        typeKind = Type ()

        typeL1, typeR1, typeL2, typeR2 :: Type TyName DefaultUni ()

        -- (all y (type) (all z (type) (fun y z)))
        typeL1 = TyForall () yName typeKind (TyForall () zName typeKind (TyFun () varY varZ))
        -- (all x (type) (all y (type) (fun x y)))
        typeR1 = TyForall () xName typeKind (TyForall () yName typeKind (TyFun () varX varY))

        -- (all z (type) (fun (all w (all x (type) (fun w x))))) z)
        typeL2
            = TyForall () zName typeKind
            $ TyFun ()
                (TyForall () wName typeKind $ TyForall () xName typeKind (TyFun () varW varX))
                varZ
        -- (all x (type) (fun (all x (all y (type) (fun x y))))) x)
        typeR2
            = TyForall () xName typeKind
            $ TyFun ()
                (TyForall () xName typeKind $ TyForall () yName typeKind (TyFun () varX varY))
                varX

    [typeL1, typeL2] @?= [typeR1, typeR2]

test_names :: TestTree
test_names =
    testGroup "names"
        [ test_DeBruijnInteresting
        , test_mangle
        , test_equalityRename
        , test_equalityBrokenRename
        , test_equalityNoMarkRename
        , test_scopingGood "renaming" (genProgram @DefaultFun) BindingRemovalNotOk PrerenameNo
            rename
        , test_scopingSpoilRenamer (genProgram @DefaultFun) markNonFreshProgram renameProgramM
        , test_alphaEquality
        , test_rebindShadowedVariable
        , test_rebindCapturedVariable
        ]
