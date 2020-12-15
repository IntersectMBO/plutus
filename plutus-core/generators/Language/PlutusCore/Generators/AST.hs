{-# LANGUAGE TypeApplications #-}

module Language.PlutusCore.Generators.AST
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

import           PlutusPrelude

import           Language.PlutusCore
import           Language.PlutusCore.Subst

import           Control.Monad.Morph       (hoist)
import           Control.Monad.Reader
import           Data.Set                  (Set)
import qualified Data.Set                  as Set
import           Hedgehog                  hiding (Size, Var)
import qualified Hedgehog.Internal.Gen     as Gen
import qualified Hedgehog.Range            as Range

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

genVersion :: MonadGen m => m (Version ())
genVersion = Version () <$> int' <*> int' <*> int' where
    int' = Gen.integral_ $ Range.linear 0 10

-- | Generate a fixed set of names which we will use, of only up to a short size to make it
-- likely that we get reuse.
-- We do not attempt not to generate reserved words such as @all@ or @abs@ as the classic syntax
-- parsers (both PLC and PIR ones) can handle names of variables clashing with reserved words.
-- In the readable syntax that would be troubling, though, but we don't have a parser for that anyway.
genNames :: MonadGen m => m [Name]
genNames = do
    let genUniq = Unique <$> Gen.int (Range.linear 0 100)
    uniqs <- Set.toList <$> Gen.set (Range.linear 1 20) genUniq
    let genText = Gen.text (Range.linear 1 4) Gen.lower
    for uniqs $ \uniq -> do
        text <- genText
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

{- Generate constant terms for each type in the default universe. The lexer
  should be able to consume escape sequences in characters and strings; both
  standard ASCII escape sequences and Unicode ones.  Hedgehog has generators for
  both of these, but the Unicode one essentially never generates anything
  readable: all of the output looks like '\857811'.  For this reason we have
  separate generators for Unicode characters and Latin-1 ones (characters 0-255,
  including standard ASCII from 0-127); there is also a generator for
  UTF8-encoded Unicode. -}
genConstant :: AstGen (Some (ValueOf DefaultUni))
genConstant= Gen.frequency
    [ (3,  someValue <$> pure ())
    , (3,  someValue <$> pure False)
    , (3,  someValue <$> pure True)
    , (10, someValue <$> Gen.latin1)   -- Character: 'c', '\n', '\SYN', \253,  etc.
    , (10, someValue <$> Gen.unicode)  -- Unicode character: typically '\857811' etc. Almost never generates anything readable.
    , (10, someValue <$> Gen.string (Range.linear 0 100) Gen.latin1)
    , (10, someValue <$> Gen.string (Range.linear 0 100) Gen.unicode)
    , (10, someValue <$> Gen.utf8   (Range.linear 0 100) Gen.unicode)
    , (10, someValue <$> Gen.bytes  (Range.linear 0 100))      -- Bytestring
    , (10, someValue <$> Gen.integral (Range.linear (-k1) k1)) -- Smallish Integers
    , (10, someValue <$> Gen.integral (Range.linear (-k2) k2)) -- Big Integers, generally not Ints
    ]
    where k1 = 1000000 :: Integer
          k2 = m*m
          m = fromIntegral (maxBound::Int) :: Integer

genType :: AstGen (Type TyName DefaultUni ())
genType = simpleRecursive nonRecursive recursive where
    varGen = TyVar () <$> genTyName
    funGen = TyFun () <$> genType <*> genType
    lamGen = TyLam () <$> genTyName <*> genKind <*> genType
    forallGen = TyForall () <$> genTyName <*> genKind <*> genType
    applyGen = TyApp () <$> genType <*> genType
    recursive = [funGen, applyGen]
    nonRecursive = [varGen, lamGen, forallGen]

genTerm :: AstGen (Term TyName Name DefaultUni DefaultFun ())
genTerm = simpleRecursive nonRecursive recursive where
    varGen = Var () <$> genName
    absGen = TyAbs () <$> genTyName <*> genKind <*> genTerm
    instGen = TyInst () <$> genTerm <*> genType
    lamGen = LamAbs () <$> genName <*> genType <*> genTerm
    applyGen = Apply () <$> genTerm <*> genTerm
    unwrapGen = Unwrap () <$> genTerm
    wrapGen = IWrap () <$> genType <*> genType <*> genTerm
    errorGen = Error () <$> genType
    recursive = [absGen, instGen, lamGen, applyGen, unwrapGen, wrapGen]
    nonRecursive = [varGen, Constant () <$> genConstant, Builtin () <$> genBuiltin, errorGen]

genProgram :: AstGen (Program TyName Name DefaultUni DefaultFun ())
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
allTermNames term = vTerm term <> Set.map coerce (tvTerm term)

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
