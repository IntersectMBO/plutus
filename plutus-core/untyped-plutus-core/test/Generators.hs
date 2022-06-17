{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Generators where

import PlutusPrelude

import PlutusCore (Name, DefaultUni, DefaultFun, nameString, runQuoteT)
import PlutusCore.Error (ParserErrorBundle)
import PlutusCore.Generators
import PlutusCore.Generators.AST as AST
import PlutusCore.Pretty
import UntypedPlutusCore.Core.Type
import UntypedPlutusCore.Parser

import Universe

import Data.Text qualified as T

import Hedgehog (tripping, property)
import Test.Tasty
import Test.Tasty.Hedgehog

import Flat qualified

-- | A 'Program' which we compare using textual equality of names rather than alpha-equivalence.
newtype TextualProgram a = TextualProgram { unTextualProgram :: Program Name DefaultUni DefaultFun a } deriving stock Show

instance Eq a => Eq (TextualProgram a) where
    (TextualProgram p1) == (TextualProgram p2) = compareProgram p1 p2

compareName :: Name -> Name -> Bool
compareName = (==) `on` nameString

compareTerm
    :: (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq a)
    => Term Name uni fun a -> Term Name uni fun a -> Bool
compareTerm (Var _ n) (Var _ n')                   = compareName n n'
compareTerm (LamAbs _ n t) (LamAbs _ n' t')        = compareName n n' && compareTerm t t'
compareTerm (Apply _ t t'') (Apply _ t' t''')      = compareTerm t t' && compareTerm t'' t'''
compareTerm (Force _ t ) (Force _ t')              = compareTerm t t'
compareTerm (Delay _ t ) (Delay _ t')              = compareTerm t t'
compareTerm (Constant _ x) (Constant _ y)          = x == y
compareTerm (Builtin _ bi) (Builtin _ bi')         = bi == bi'
compareTerm (Error _ ) (Error _ )                  = True
compareTerm _ _                                    = False

compareProgram
    :: (GEq uni, Closed uni, uni `Everywhere` Eq, Eq fun, Eq a)
    => Program Name uni fun a -> Program Name uni fun a -> Bool
compareProgram (Program _ v t) (Program _ v' t') = v == v' && compareTerm t t'

genProgram :: forall fun. (Bounded fun, Enum fun) => AstGen (Program Name DefaultUni fun ())
genProgram = fmap eraseProgram AST.genProgram

propFlat :: TestTree
propFlat = testProperty "Flat" $ property $ do
    prog <- forAllPretty $ runAstGen (Generators.genProgram @DefaultFun)
    tripping prog Flat.flat Flat.unflat

propParser :: TestTree
propParser = testProperty "Parser" $ property $ do
    prog <- TextualProgram <$> forAllPretty (runAstGen Generators.genProgram)
    tripping prog (displayPlcDef . unTextualProgram)
                (\p -> fmap (TextualProgram . void) (parseProg p))
    where
        parseProg :: T.Text -> Either ParserErrorBundle (Program Name DefaultUni DefaultFun SourcePos)
        parseProg p = runQuoteT $ parseProgram p

test_parsing :: TestTree
test_parsing = testGroup "Parsing"
               [ propFlat
               , propParser
               ]
