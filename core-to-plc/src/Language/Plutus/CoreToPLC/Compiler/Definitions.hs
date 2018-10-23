{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Plutus.CoreToPLC.Compiler.Definitions where

import           Language.Plutus.CoreToPLC.Error
import           Language.Plutus.CoreToPLC.PLCTypes

import qualified Language.PlutusCore                as PLC
import           Language.PlutusCore.MkPlc

import qualified GhcPlugins                         as GHC

import           Control.Monad.Except

import           Data.Foldable
import qualified Data.Graph                         as Graph
import qualified Data.Map                           as Map
import           Data.Maybe                         (fromMaybe)

-- | The visibility of a definition. See Note [Abstract data types]
data Visibility = Abstract | Visible
-- | A definition of type 'val' with variable type 'var'.
data Def var val = Def {dVis::Visibility, dVar::var, dVal::val}

isVisible :: Def var val -> Bool
isVisible (Def vis _ _) = case vis of
    Abstract -> False
    Visible  -> True

-- | Either a simple type or a datatype with constructors and a matcher.
data TypeRep = PlainType PLCType | DataType PLCType [TermDef] TermDef

trTy :: TypeRep -> PLCType
trTy = \case
    PlainType t -> t
    DataType t _ _ -> t

type TypeDef = Def PLCTyVar TypeRep

tydTy :: TypeDef -> PLCType
tydTy = \case
    Def Abstract (PLCTyVar n _) _ -> PLC.TyVar () n
    Def Visible _ tr -> trTy tr

tydConstrs :: TypeDef -> Maybe [TermDef]
tydConstrs = \case
    Def _ _ (DataType _ constrs _) -> Just constrs
    _ -> Nothing

tydMatch :: TypeDef -> Maybe TermDef
tydMatch = \case
    Def _ _ (DataType _ _ match) -> Just match
    _ -> Nothing

type TermDef = Def PLCVar PLCTerm

tdTerm :: TermDef -> PLCTerm
tdTerm = \case
    Def Abstract (PLCVar n _) _ -> PLC.Var () n
    Def Visible _ t -> t

type DefMap key def = Map.Map key (def, [key])

-- Processing definitions

data TermOrTypeDef = TermDef TermDef | TypeDef TypeDef

-- | Given the definitions in the program, create a topologically ordered list of the SCCs using the dependency information
defSccs :: DefMap GHC.Name TypeDef -> DefMap GHC.Name TermDef -> [Graph.SCC TermOrTypeDef]
defSccs typeDefs termDefs =
    let
        typeInputs = fmap (\(ghcName, (d, deps)) -> (TypeDef d, ghcName, deps)) (Map.assocs typeDefs)
        termInputs = fmap (\(ghcName, (d, deps)) -> (TermDef d, ghcName, deps)) (Map.assocs termDefs)
    in
        -- weirdly this produces them in reverse topological order
        reverse $ Graph.stronglyConnComp (typeInputs ++ termInputs)

wrapWithDefs
    :: (MonadError ConvError m)
    => DefMap GHC.Name TypeDef
    -> DefMap GHC.Name TermDef
    -> PLC.Term PLC.TyName PLC.Name ()
    -> m (PLC.Term PLC.TyName PLC.Name ())
wrapWithDefs typeDefs termDefs body = do
    let sccs = defSccs typeDefs termDefs
    -- process from the inside out
    foldM wrapDefScc body (reverse sccs)

wrapDefScc
    :: (MonadError ConvError m)
    => PLC.Term PLC.TyName PLC.Name ()
    -> Graph.SCC TermOrTypeDef
    -> m (PLC.Term PLC.TyName PLC.Name ())
wrapDefScc acc scc = case scc of
    Graph.AcyclicSCC def            -> pure $ wrapDef acc def
    -- self-recursive types are okay, but we don't handle recursive groups of definitions in general at the moment
    Graph.CyclicSCC [def@TypeDef{}] -> pure $ wrapDef acc def
    Graph.CyclicSCC _               -> throwPlain $ UnsupportedError "Mutually recursive definitions not currently supported"

-- | Wrap a term with a single definition.
wrapDef :: PLC.Term PLC.TyName PLC.Name () -> TermOrTypeDef -> PLC.Term PLC.TyName PLC.Name ()
wrapDef term def = case def of
    TypeDef d ->
        -- See Note [Abstract data types]
        let
            constructors = fromMaybe [] $ tydConstrs d
            destructors = toList $ tydMatch d
            -- we don't bother binding things that are not abstract since they will have
            -- been inlined
            abstractTys = filter (not . isVisible) [d]
            abstractTerms = filter (not . isVisible) (constructors ++ destructors)
            tyVars = fmap (splitTyVar . dVar) abstractTys
            tys = fmap (trTy . dVal) abstractTys
            vars = fmap (splitVar . dVar) abstractTerms
            vals = fmap dVal abstractTerms
        in
            mkIterApp (mkIterInst (mkIterTyAbs tyVars (mkIterLamAbs vars term)) tys) vals
    TermDef (Def _ (PLCVar n ty) rhs) -> mkTermLet n rhs ty term
