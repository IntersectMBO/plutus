{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module Names.Spec where

import PlutusCore (DefaultFun, DefaultUni, FreeVariableError, Kind (Type), Name (..), NamedDeBruijn,
                   NamedTyDeBruijn, Program, Quote, Rename (rename), Term (..), TyName (..),
                   Type (..), Unique (..), deBruijnTerm, runQuote, runQuoteT, unDeBruijnTerm)
import PlutusCore qualified
import PlutusCore.Error qualified as PLC
import PlutusCore.Generators.Hedgehog (TermOf (..), forAllNoShowT, forAllPretty, generalizeT)
import PlutusCore.Generators.Hedgehog.AST as AST (genName, genProgram, genTerm, mangleNames,
                                                  runAstGen)
import PlutusCore.Generators.Hedgehog.Interesting (fromInterestingTermGens)
import PlutusCore.Mark (markNonFreshProgram)
import PlutusCore.Parser qualified as Parser
import PlutusCore.Pretty (display, displayPlcSimple)
import PlutusCore.Rename.Internal (renameProgramM)
import PlutusCore.Test (BindingRemoval (BindingRemovalNotOk), Prerename (PrerenameNo), brokenRename,
                        checkFails, mapTestLimitAtLeast, noMarkRename, test_scopingGood,
                        test_scopingSpoilRenamer)

import Control.Monad.Except (modifyError)
import Data.String (IsString (fromString))
import Data.Text qualified as Text
import Hedgehog (Gen, Property, forAll, property, tripping, (/==), (===))
import Hedgehog.Gen qualified as Gen
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testPropertyNamed)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

prop_DeBruijn :: Gen (TermOf (Term TyName Name DefaultUni DefaultFun ()) a) -> Property
prop_DeBruijn gen = property $ generalizeT do
  TermOf body _ <- forAllNoShowT gen
  let
    forward = deBruijnTerm
    backward
      :: Either FreeVariableError (Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun a)
      -> Either FreeVariableError (Term TyName Name DefaultUni DefaultFun a)
    backward e = e >>= runQuoteT . unDeBruijnTerm
  tripping body forward backward

test_DeBruijnInteresting :: TestTree
test_DeBruijnInteresting =
  testGroup "de Bruijn transformation round-trip" $
    fromInterestingTermGens \name ->
      testPropertyNamed name (fromString name)
        . mapTestLimitAtLeast 99 (`div` 10)
        . prop_DeBruijn

test_mangle :: TestTree
test_mangle =
  testPropertyNamed "equality does not survive mangling" "equality_mangling" . property $ do
    (term, termMangled) <- forAll . runAstGen . Gen.justT $ do
      term <- AST.genTerm
      mayTermMang <- mangleNames term
      pure $ (,) term <$> mayTermMang
    term /== termMangled
    termMangled /== term

-- | Test equality of a program and its renamed version, given a renamer.
prop_equalityFor
  :: program ~ Program TyName Name DefaultUni DefaultFun ()
  => (program -> Quote program)
  -> Property
prop_equalityFor ren = property do
  prog <- forAllPretty $ runAstGen genProgram
  let progRen = runQuote $ ren prog
  progRen === prog
  prog === progRen

test_equalityRename :: TestTree
test_equalityRename =
  testPropertyNamed "equality survives renaming" "equality_renaming" $
    prop_equalityFor rename

test_equalityBrokenRename :: TestTree
test_equalityBrokenRename =
  testCase "equality does not survive wrong renaming" $
    checkFails . prop_equalityFor $
      brokenRename markNonFreshProgram renameProgramM

test_equalityNoMarkRename :: TestTree
test_equalityNoMarkRename =
  testCase "equality does not survive renaming without marking" $
    checkFails . prop_equalityFor $
      noMarkRename renameProgramM

test_alphaEquality :: TestTree
test_alphaEquality = testCase "alphaEquality" do
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
test_rebindShadowedVariable = testCase "rebindShadowedVariable" do
  let
    xName = TyName (Name "x" (Unique 0))
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

    err =
      concat
        [ displayPlcSimple l2
        , " and "
        , displayPlcSimple r2
        , " are supposed not to be equal, but they are equal"
        ]

  l1 @?= r1
  assertBool err $ l2 /= r2

test_rebindCapturedVariable :: TestTree
test_rebindCapturedVariable = testCase "rebindCapturedVariable" do
  let
    wName = TyName (Name "w" (Unique 0))
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
    typeL2 =
      TyForall () zName typeKind $
        TyFun
          ()
          (TyForall () wName typeKind $ TyForall () xName typeKind (TyFun () varW varX))
          varZ
    -- (all x (type) (fun (all x (all y (type) (fun x y))))) x)
    typeR2 =
      TyForall () xName typeKind $
        TyFun
          ()
          (TyForall () xName typeKind $ TyForall () yName typeKind (TyFun () varX varY))
          varX

  [typeL1, typeL2] @?= [typeR1, typeR2]

test_printing_parsing_roundtrip :: TestTree
test_printing_parsing_roundtrip =
  testPropertyNamed
    "Printing/parsing roundtrip"
    "name_print_parse_roundtrip"
    prop_printing_parsing_roundtrip

prop_printing_parsing_roundtrip :: Property
prop_printing_parsing_roundtrip = property $ generalizeT do
  name <- forAllPretty $ runAstGen genName
  tripping name display parse
  where
    parse :: String -> Either (PlutusCore.Error DefaultUni DefaultFun ()) Name
    parse str = runQuoteT $ modifyError PLC.ParseErrorE $ do
      Parser.parse Parser.name "test_printing_parsing_roundtrip" (Text.pack str)

test_names :: TestTree
test_names =
  testGroup
    "names"
    [ test_DeBruijnInteresting
    , test_mangle
    , test_equalityRename
    , test_equalityBrokenRename
    , test_equalityNoMarkRename
    , test_scopingGood "renaming" (genProgram @DefaultFun) BindingRemovalNotOk PrerenameNo rename
    , test_scopingSpoilRenamer (genProgram @DefaultFun) markNonFreshProgram renameProgramM
    , test_alphaEquality
    , test_rebindShadowedVariable
    , test_rebindCapturedVariable
    , test_printing_parsing_roundtrip
    ]
