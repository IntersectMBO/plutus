-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module PlutusCore.Generators.Hedgehog.AST
    ( simpleRecursive
    , AstGen
    , runAstGen
    , genVersion
    , genNames
    , genName
    , genTyName
    , genKind
    , genBuiltin
    , genConstant
    , genType
    , genTerm
    , genProgram
    , mangleNames
    ) where

import PlutusPrelude

import PlutusCore
import PlutusCore.Name (isQuotedIdentifierChar)
import PlutusCore.Subst

import Control.Lens (coerced)
import Control.Monad.Morph (hoist)
import Control.Monad.Reader
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Set.Lens (setOf)
import Data.Text (Text)
import Data.Text qualified as Text
import Hedgehog hiding (Size, Var)
import Hedgehog.Internal.Gen qualified as Gen
import Hedgehog.Range qualified as Range

simpleRecursive :: MonadGen m => [m a] -> [m a] -> m a
simpleRecursive = Gen.recursive Gen.choice

{- Note [ScopeHandling]
We intentionally do not distinguish between the type-level and term-level scopes to ensure that
all the machineries handle variables with same uniques from distinct scopes correctly.
-}

-- See Note [ScopeHandling].
-- | The monad that generators run in. The environment is a list of names to choose from for
-- generation of variables and binders.
type AstGen = GenT (Reader [Name])

runAstGen :: MonadGen m => AstGen a -> m a
runAstGen a = do
    names <- genNames
    Gen.fromGenT $ hoist (return . flip runReader names) a

-- The parser will reject uses of new constructs if the version is not high enough
-- In order to keep our lives simple, we just generate a version that is always high
-- enough to support everything. That gives us less coverage of parsing versions, but
-- that's not likely to be the place where things go wrong
genVersion :: MonadGen m => m Version
genVersion = Version <$> intFrom 1 <*> intFrom 1 <*> intFrom 0 where
    intFrom x = Gen.integral_ $ Range.linear x 20

genNameText :: MonadGen m => m Text
genNameText = Gen.choice [genUnquoted, genQuoted]
  where
    genUnquoted =
        Text.cons
            <$> Gen.alpha
            <*> Gen.text (Range.linear 0 4) (Gen.choice [Gen.alphaNum, Gen.element ['_', '\'']])
    genQuoted =
        Gen.text (Range.linear 1 5) (Gen.filterT isQuotedIdentifierChar Gen.ascii)

-- | Generate a fixed set of names which we will use, of only up to a short size to make it
-- likely that we get reuse.
-- We do not attempt not to generate reserved words such as @all@ or @abs@ as the classic syntax
-- parsers (both PLC and PIR ones) can handle names of variables clashing with reserved words.
-- In the readable syntax that would be troubling, though, but we don't have a parser for that anyway.
genNames :: MonadGen m => m [Name]
genNames = do
    let genUniq = Unique <$> Gen.int (Range.linear 0 100)
    uniqs <- Set.toList <$> Gen.set (Range.linear 1 20) genUniq
    for uniqs $ \uniq -> do
        text <- genNameText
        return $ Name text uniq

genName :: AstGen Name
genName = ask >>= Gen.element

genTyName :: AstGen TyName
genTyName = TyName <$> genName

genKind :: AstGen (Kind ())
genKind = simpleRecursive nonRecursive recursive where
    nonRecursive = pure <$> sequence [Type] ()
    recursive = [KindArrow () <$> genKind <*> genKind]

genBuiltin :: (Bounded fun, Enum fun) => AstGen fun
genBuiltin = Gen.element [minBound .. maxBound]

genConstant :: AstGen (Some (ValueOf DefaultUni))
genConstant = Gen.choice
    [ pure (someValue ())
    , someValue @Integer <$> Gen.integral_ (Range.linear (-10000000) 10000000)
    , someValue <$> Gen.utf8 (Range.linear 0 40) Gen.unicode
    ]

-- We only generate types that are parsable. See Note [Parsing horribly broken].
genSomeTypeIn :: AstGen (SomeTypeIn DefaultUni)
genSomeTypeIn = Gen.frequency
    [ (1, pure $ SomeTypeIn DefaultUniInteger)
    , (1, pure $ SomeTypeIn DefaultUniByteString)
    , (1, pure $ SomeTypeIn DefaultUniString)
    , (1, pure $ SomeTypeIn DefaultUniUnit)
    , (1, pure $ SomeTypeIn DefaultUniBool)
    ]

genType :: AstGen (Type TyName DefaultUni ())
genType = simpleRecursive nonRecursive recursive where
    varGen = TyVar () <$> genTyName
    funGen = TyFun () <$> genType <*> genType
    lamGen = TyLam () <$> genTyName <*> genKind <*> genType
    forallGen = TyForall () <$> genTyName <*> genKind <*> genType
    applyGen = TyApp () <$> genType <*> genType
    sopGen = TySOP () <$> (Gen.list (Range.linear 0 10) (Gen.list (Range.linear 0 10) genType))
    tyBuiltinGen = TyBuiltin () <$> genSomeTypeIn
    recursive = [funGen, applyGen, sopGen]
    nonRecursive = [varGen, lamGen, forallGen, tyBuiltinGen]

genTerm :: forall fun. (Bounded fun, Enum fun) => AstGen (Term TyName Name DefaultUni fun ())
genTerm = simpleRecursive nonRecursive recursive where
    varGen = Var () <$> genName
    absGen = TyAbs () <$> genTyName <*> genKind <*> genTerm
    instGen = TyInst () <$> genTerm <*> genType
    lamGen = LamAbs () <$> genName <*> genType <*> genTerm
    applyGen = Apply () <$> genTerm <*> genTerm
    unwrapGen = Unwrap () <$> genTerm
    wrapGen = IWrap () <$> genType <*> genType <*> genTerm
    errorGen = Error () <$> genType
    constrGen = Constr () <$> genType <*> Gen.word64 (Range.linear 0 10) <*> Gen.list (Range.linear 0 10) genTerm
    caseGen = Case () <$> genType <*> genTerm <*> Gen.list (Range.linear 0 10) genTerm
    recursive = [absGen, instGen, lamGen, applyGen, unwrapGen, wrapGen, constrGen, caseGen]
    nonRecursive = [varGen, Constant () <$> genConstant, Builtin () <$> genBuiltin, errorGen]

genProgram :: forall fun. (Bounded fun, Enum fun) => AstGen (Program TyName Name DefaultUni fun ())
genProgram = Program () <$> genVersion <*> genTerm

{- Note [Name mangling]
We want to test that turning a term into a distinct one results in a failed equality check.
For this we keep the spine of the term the same, but change some of its variables at their
usage sites. Variables that are going to be changed are selected before the mangling happens,
so that this subset of term's variables can be easily controlled and is dependent on the size
parameter of the generator. Once variables are selected, the next step is to generate some new
variables none of which is a member of the set of variables prepared for mangling (but the new
variables are allowed to overlap with those that the term already contains and that are not
going to be mangled). The last step is to actually mangle the term by replacing /each usage
of a variable/ from the prepared set of variables with a /random/ variable from the set of new
variables. This way we get diverse and interesting mangled terms.
-}

subset1 :: (MonadGen m, Ord a) => Set a -> m (Maybe (Set a))
subset1 s
    | null xs   = return Nothing
    | otherwise = fmap (Just . Set.fromList) $ (:) <$> Gen.element xs <*> Gen.subsequence xs
    where xs = Set.toList s

substAllNames
    :: Monad m
    => (Name -> m (Maybe Name))
    -> Term TyName Name DefaultUni DefaultFun ()
    -> m (Term TyName Name DefaultUni DefaultFun ())
substAllNames ren =
    termSubstNamesM (fmap (fmap $ Var ()) . ren) >=>
    termSubstTyNamesM (fmap (fmap $ TyVar () . TyName) . ren . unTyName)

-- See Note [ScopeHandling].
allTermNames :: Term TyName Name DefaultUni DefaultFun () -> Set Name
allTermNames = setOf (vTerm <^> tvTerm . coerced)

-- See Note [Name mangling]
mangleNames :: Term TyName Name DefaultUni DefaultFun () -> AstGen (Maybe (Term TyName Name DefaultUni DefaultFun ()))
mangleNames term = do
    let names = allTermNames term
    mayNamesMangle <- subset1 names
    for mayNamesMangle $ \namesMangle -> do
        let isNew name = not $ name `Set.member` namesMangle
        newNames <- Gen.justT $ ensure (not . null) . filter isNew <$> genNames
        let mang name
                | name `Set.member` namesMangle = Just <$> Gen.element newNames
                | otherwise                     = return Nothing
        substAllNames mang term
