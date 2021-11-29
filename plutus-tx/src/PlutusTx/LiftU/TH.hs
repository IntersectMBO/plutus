-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE TemplateHaskell #-}
module PlutusTx.LiftU.TH where

import UntypedPlutusCore qualified as UPLC

import Data.Foldable
import Data.Set qualified as Set
import Data.Traversable

import Control.Monad.State
import Control.Monad.Writer

import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH

import PlutusTx.Lift.THUtils
import PlutusTx.LiftU.Class

import PlutusCore qualified as PLC

-- We do not use qualified import because the whole module contains off-chain code
import Prelude

type Deps = Set.Set TH.Type

type LiftTHM a = StateT Deps TH.Q a

addDep :: TH.Type -> LiftTHM ()
addDep ty = do
    ty' <- lift $ normalizeAndResolve ty
    modify $ Set.insert ty'

newtypeLiftUClause :: TH.ConstructorInfo -> LiftTHM TH.Clause
newtypeLiftUClause TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=[argTy]} = do
    addDep argTy
    argName <- lift $ TH.newName "arg"
    let body = [| (liftU $(TH.varE argName)) |]
    lift $ TH.clause [TH.conP name [TH.varP argName]] (TH.normalB body) []
newtypeLiftUClause _ = fail "Newtypes should have only one argument"

liftUClause :: (TH.ConstructorInfo, Int) -> LiftTHM TH.Clause
liftUClause (TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys}, index) = do
    traverse_ addDep argTys
    argNames <- for argTys $ \_ -> lift $ TH.newName "arg"
    let argsList = TH.listE $ map (\v -> [| liftU $(TH.varE v) |]) argNames
    let ctr = [| UPLC.Constr () index $argsList |]
    lift $ TH.clause [TH.conP name (fmap TH.varP argNames)] (TH.normalB ctr) []

reconstructMatch :: (TH.ConstructorInfo, Int) -> LiftTHM TH.Match
reconstructMatch (TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys}, index) = do
    traverse_ addDep argTys
    argNames <- for (zip argTys [0..]) $ \(_, i :: Int) -> lift $ TH.newName ("arg" ++ show i)

    -- Applicatively build the constructor application, assuming that all the arguments are in scope
    body <- lift $ foldl' (\h v -> [| $h <*> unliftU $(TH.varE v) |]) [| pure $(TH.conE name) |] argNames

    pat <- lift [p| UPLC.Constr _ $(TH.litP $ TH.IntegerL $ fromIntegral index) $(TH.listP $ fmap TH.varP argNames) |]

    pure $ TH.Match pat (TH.NormalB body) []

unliftUClause :: [(TH.ConstructorInfo, Int)] -> LiftTHM TH.Clause
unliftUClause indexedCons = do
    dName <- lift $ TH.newName "d"
    -- Call the clause for each constructor, falling through to the next one, until we get to the end in which case we return 'Nothing'
    matches <- traverse reconstructMatch indexedCons
    fallthrough <- lift $ TH.match TH.wildP (TH.normalB [| Nothing |]) []
    let body = TH.CaseE (TH.VarE dName) (matches ++ [fallthrough])
    pure $ TH.Clause [TH.VarP dName] (TH.NormalB body) []

newtypeUnliftUClause :: [TH.ConstructorInfo] -> LiftTHM TH.Clause
newtypeUnliftUClause [TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=[argTy]}] = do
    addDep argTy
    dName <- lift $ TH.newName "d"
    body <- lift [| fmap $(TH.conE name) (unliftU $(TH.varE dName)) |]
    pure $ TH.Clause [TH.VarP dName] (TH.NormalB body) []
newtypeUnliftUClause _ = fail "Newtype should have only one constructor with only one argument"

-- TODO: what *should* this be? it should match up with what the compiler does, for sure...
defaultIndex :: TH.Name -> TH.Q [(TH.Name, Int)]
defaultIndex name = do
    info <- TH.reifyDatatype name
    pure $ zip (TH.constructorName <$> TH.datatypeCons info) [0..]

-- | Generate a 'LiftU' and a 'UnliftU' instance for a type. This uses the order of the constructors in the declaration,
-- which matches what the Plutus Tx compiler will use, and is probably what you want.
--
-- Generates an instance pinned to the default values for @name@, @uni@, and @fun@, you may want to write a
-- version by hand if this is a problem.
defaultMakeLiftU :: TH.Name -> TH.Q [TH.Dec]
defaultMakeLiftU name = makeLiftUIndexed name =<< defaultIndex name

-- | Generate a 'LiftU' and a 'UnliftU' instance for a type, using an explicit mapping of constructor names to indices. Use
-- this if you need to control which constructor gets which index.
--
-- Generates an instance pinned to the default values for @name@, @uni@, and @fun@, you may want to write a
-- version by hand if this is a problem.
makeLiftUIndexed :: TH.Name -> [(TH.Name, Int)] -> TH.Q [TH.Dec]
makeLiftUIndexed name indices = do

    info <- TH.reifyDatatype name
    let appliedType = TH.datatypeType info

    -- TODO: this is dissatisfying. We should be able to generate generic instances
    -- and the main reason we don't (same for Lift) is that it's annoying then to know what
    -- constraints to include. This way we can be sure that we don't need any constraints
    -- for concrete types.
    n <- TH.newName "n"
    let nameT = TH.VarT n
    let uniT = TH.ConT ''PLC.DefaultUni
    let funT = TH.ConT ''PLC.DefaultFun

    indexedCons <- for (TH.datatypeCons info) $ \c -> case lookup (TH.constructorName c) indices of
            Just i  -> pure (c, i)
            Nothing -> fail $ "No index given for constructor" ++ show (TH.constructorName c)

    let datatypeType = TH.datatypeType info

    let mkLiftUPred ty = TH.classPred ''LiftU [nameT, uniT, funT, ty]
    let mkUnliftUPred ty = TH.classPred ''UnliftU [nameT, uniT, funT, ty]

    -- TODO: if the type is a newtype then it should not have a constructor added
    -- seems tricky to make this work, the other option is to emit an error here and tell the
    -- user to use newtype-deriving manually?
    liftUInst <- do
        (clauses, deps) <- flip runStateT mempty $
          if isNewtype info
          then traverse newtypeLiftUClause (fmap fst indexedCons)
          else traverse liftUClause indexedCons

        let prunedDeps = Set.delete datatypeType deps

        -- See Note [Closed constraints]
        let constraints = fmap mkLiftUPred . filter (not . isClosedType) $ Set.toList prunedDeps

        let liftUDecl = TH.FunD 'liftU clauses
        pure $ TH.InstanceD Nothing constraints (mkLiftUPred appliedType) [liftUDecl]

    unliftUInst <- do
        (clause, deps) <- flip runStateT mempty $
          if isNewtype info
          then newtypeUnliftUClause (fmap fst indexedCons)
          else unliftUClause indexedCons

        let prunedDeps = Set.delete datatypeType deps

        -- See Note [Closed constraints]
        let constraints = fmap mkUnliftUPred . filter (not . isClosedType) $ Set.toList prunedDeps

        let unliftUDecl = TH.FunD 'unliftU [clause]
        pure $ TH.InstanceD Nothing constraints (mkUnliftUPred appliedType) [unliftUDecl]

    pure [liftUInst, unliftUInst]
