-- editorconfig-checker-disable-file
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}

module PlutusIR.Analysis.RetainedSize
    ( RetainedSize (..)
    , Size (..)
    , termRetentionMap
    , annotateWithRetainedSize
    ) where

import PlutusPrelude

import PlutusIR.Analysis.Dependencies
import PlutusIR.Analysis.Size
import PlutusIR.Core

import PlutusCore qualified as PLC
import PlutusCore.Builtin as PLC
import PlutusCore.Name

import Algebra.Graph qualified as C
import Algebra.Graph.ToGraph
import Control.Lens
import Data.Graph.Dom (domTree)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Tree

{- Note [Retained size analysis]
WARNING: everything in this module assumes global uniqueness of variables.

For calculating the size that each binding retains we use a classic graph algorithm for dominance.
The @algebraic-graphs@ library does not provide one out of the box, so we convert an algebraic graph
to a @fgl@-based representation and use the @dom-lt@ library for calculating the dominator tree
(note that @fgl@ itself has an algorithm for dominance [1], but that was only found out after
everything below was implemented, plus that algorithm does not return a 'Tree', so it's not as
convenient to use).

The procedure for computing the retained size of each binding is two-staged:

1. First we compute how much size each let-binding in a term retains directly.
   For example, a 'TermBind' directly retains only the type signature and the body of the binding.
2. Then we compute the dominator tree for the dependency graph of the term and annotate it with the
   retained size of each binding by adding up the directly retained size of the binding computed at
   stage one and the size retained by all the dependencies of the binding

We don't make any assumptions as to whether, say, a constructor of a data type directly retains the
entire data type (its other constructors, the kind signature of the data type etc). Instead, we
specify that each constructor directly retains only its type signature, each parameter directly
retains only its kind signature etc and we let dependency and dominator tree analysis figure out
whether the constructor in fact retains the entire data type by virtue of the constructor being
connected (or not connected) with other parts of the data type. This has a funny effect: if only
one constructor of the data type is actually used, then it's closer to the root of the dependency
graph and so every other part of the data type is considered a dependency (due to them all being
interconnected) and so that constructor gets annotated with the size of the whole data type, while
every other constructor is only annotated with the size that it directly retains (i.e. the size of
its type signature).

Our main motivation for implementing retained size analysis is to calculate what bindings retain
most size, so that we can prioritize certain optimization passes, however we mostly care about the
size of the final untyped program and given that we do take types and kinds into account during
retained size analysis, results do not translate directly to the untyped setting. So beware of this
pitfall.

Even the most efficient dominator tree algorithms are still not linear and our programs are quite
huge, so before jumping into computing the dominator tree we filter the dependency graph and remove
from it everything that does not directly retain any size, i.e. everything that is not a let-binding.
For example, the dependency graph contains lambda-bound variables and we filter them out as they're
irrelevant for computing dominance. So we're relying on the fact that nodes that don't retain any
size are also not interesting for dominator analysis. Which might be wrong. An example is needed.

[1] https://hackage.haskell.org/package/fgl-5.7.0.3/docs/Data-Graph-Inductive-Query-Dominators.html#v:dom
-}

{- Note [Handling the root]
The dominator tree algorithm works on the assumption that each node is an 'Int'. It's easy to
convert the 'Unique' of a variable to an 'Int', but the dominator tree algorithm needs a root to
walk from and that root also has to be an 'Int' and our uniques start from zero, so we made an
awkward decision to assign the root @-1@ as its index.

Given that the root appears in the dominator tree, we also need to specify the size that it directly
retains. But there doesn't seem to be a sensible way of doing that. Should it be

    rootSize :: Term tyname name uni fun ann -> Size
    rootSize (Let _ _ _ term) = rootSize term
    rootSize term             = termSize term

? But what about bindings inside the final non-let term? However we don't need that directly
retained size of the root for anything that is not "don't throw an error on encountering the root
node that does not correspond to any binding" and since we only annotate bindings, the size retained
by the root is not supposed to appear in the final annotated term anyway, so we just make the root
directly retain some ridiculously huge _negative_ number. Now if it ends up being in the final term,
we know there's a bug somewhere and if it doesn't, we don't care about it.
-}

data RetainedSize
    = Retains Size
    | NotARetainer
    deriving stock (Show)

instance Pretty RetainedSize where
    pretty (Retains size) = "$" <> pretty size <> "$"
    pretty NotARetainer   = mempty

-- See Note [Handling the root].
-- | The 'Int' index of the root.
rootInt :: Int
rootInt = -1

-- See Note [Handling the root].
nodeToInt :: Node -> Int
nodeToInt (Variable (PLC.Unique i)) = i
nodeToInt Root                      = rootInt

-- | A mapping from the index of a binding to what it directly retains.
newtype DirectionRetentionMap = DirectionRetentionMap (IntMap Size)

lookupSize :: Int -> DirectionRetentionMap -> Size
lookupSize i (DirectionRetentionMap ss) = ss IntMap.! i

-- | Annotate the dominator tree with the retained size of each entry. The retained size is computed
-- as the size directly retained by the binding plus the size of all its dependencies.
annotateWithSizes :: DirectionRetentionMap -> Tree Int -> Tree (Int, Size)
annotateWithSizes sizeInfo = go where
    go (Node i ts) = Node (i, sizeI) rs where
        rs = map go ts
        sizeI = lookupSize i sizeInfo <> foldMap (snd . rootLabel) rs

-- | Compute the dominator tree of a graph.
toDomTree :: C.Graph Node -> Tree Int
toDomTree = domTree . (,) rootInt . adjacencyIntMap . fmap nodeToInt

-- | Compute the retention map of a graph.
depsRetentionMap :: DirectionRetentionMap -> C.Graph Node -> IntMap Size
depsRetentionMap sizeInfo = IntMap.fromList . flatten . annotateWithSizes sizeInfo . toDomTree

-- | Construct a 'UniqueMap' having size information for each individual part of a 'Binding'.
bindingSize
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique)
    => Binding tyname name uni fun ann -> UniqueMap Unique Size
bindingSize (TermBind _ _ var term) =
    insertByNameIndex var (varDeclSize var <> termSize term) mempty
bindingSize (TypeBind _ tyVar ty) =
    insertByNameIndex tyVar (tyVarDeclSize tyVar <> typeSize ty) mempty
bindingSize (DatatypeBind _ (Datatype _ dataDecl params matchName constrs))
    = insertByNameIndex dataDecl (tyVarDeclSize dataDecl)
    . flip (foldr $ \param -> insertByNameIndex param $ tyVarDeclSize param) params
    . insertByNameIndex matchName (Size 1)
    . flip (foldr $ \constr -> insertByNameIndex constr $ varDeclSize constr) constrs
    $ mempty

-- | Construct a 'UniqueMap' having size information for each individual part of every 'Binding'
-- in a term.
bindingSizes
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique)
    => Term tyname name uni fun ann -> UniqueMap Unique Size
bindingSizes (Let _ _ binds term) = foldMap bindingSize binds <> bindingSizes term
bindingSizes term                 = term ^. termSubterms . to bindingSizes

-- | Same as 'bindingSizes' but is wrapped in a newtype and has a bogus entry for the root.
toDirectionRetentionMap
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique)
    => Term tyname name uni fun ann -> DirectionRetentionMap
toDirectionRetentionMap term =
    DirectionRetentionMap . IntMap.insert rootInt rootSize . unUniqueMap $ bindingSizes term where
        -- See Note [Handling the root].
        rootSize = Size (- 10 ^ (10::Int))

-- | Check if a 'Node' appears in 'DirectionRetentionMap'.
hasSizeIn :: DirectionRetentionMap -> Node -> Bool
hasSizeIn _             Root                                   = True
hasSizeIn (DirectionRetentionMap ss) (Variable (PLC.Unique i)) = i `IntMap.member` ss

-- | Compute the retention map of a term.
termRetentionMap
    :: (HasUnique tyname TypeUnique, HasUnique name TermUnique, ToBuiltinMeaning uni fun)
    => PLC.BuiltinSemanticsVariant fun
    -> Term tyname name uni fun ann
    -> IntMap Size
termRetentionMap semvar term = depsRetentionMap sizeInfo deps where
    sizeInfo = toDirectionRetentionMap term
    deps = C.induce (hasSizeIn sizeInfo) $ fst $ runTermDeps semvar term

-- | Apply a function to the annotation of each part of every 'Binding' in a term.
reannotateBindings
    :: (HasUnique name TermUnique, HasUnique tyname TypeUnique)
    => (Unique -> ann -> ann)
    -> Term tyname name uni fun ann
    -> Term tyname name uni fun ann
reannotateBindings f = goTerm where
    -- We don't need these helper functions anywhere else, so we make them into local definitions.
    goVarDecl (VarDecl ann name ty) = VarDecl (f (name ^. theUnique) ann) name ty
    goTyVarDecl (TyVarDecl ann tyname kind) = TyVarDecl (f (tyname ^. theUnique) ann) tyname kind
    goDatatype (Datatype ann dataTyDecl paramTyDecls matchName constrDecls) =
        Datatype
            -- We don't have any other suitable place to associate the name of the matcher with an
            -- annotation, so we do it here. Fortunately, the matcher is the only thing that
            -- survives erasure, so this even makes some sense.
            (f (matchName ^. theUnique) ann)
            (goTyVarDecl dataTyDecl)
            (goTyVarDecl <$> paramTyDecls)
            matchName
            (goVarDecl <$> constrDecls)

    -- Note that @goBind@ and @goTerm@ are mutually recursive.
    goBind (TermBind ann str var term) = TermBind ann str (goVarDecl var) $ goTerm term
    goBind (TypeBind ann tyVar ty)     = TypeBind ann (goTyVarDecl tyVar) ty
    goBind (DatatypeBind ann datatype) = DatatypeBind ann $ goDatatype datatype

    goTerm (Let ann recy binds term) = Let ann recy (goBind <$> binds) $ goTerm term
    goTerm term                      = term & termSubterms %~ goTerm

-- Ideally we should have a separate step putting uniques into annotations, so that we can reuse it
-- both here and for scoping analysis.
-- See Note [Retained size analysis]
-- | Annotate each part of every 'Binding' in a term with the size that it retains.
annotateWithRetainedSize
    :: (HasUnique name TermUnique, HasUnique tyname TypeUnique, ToBuiltinMeaning uni fun)
    => PLC.BuiltinSemanticsVariant fun
    -> Term tyname name uni fun ann
    -> Term tyname name uni fun RetainedSize
-- @reannotateBindings@ only processes annotations "associated with" a unique, so it can't change
-- the type. Therefore we need to set all the bindings to an appropriate type beforehand.
annotateWithRetainedSize semvar term = reannotateBindings (upd . unUnique) $ NotARetainer <$ term where
    retentionMap = termRetentionMap semvar term
    -- If a binding is not in the retention map, then it's still a retainer, just retains zero size.
    upd i _ = Retains $ IntMap.findWithDefault (Size 0) i retentionMap
