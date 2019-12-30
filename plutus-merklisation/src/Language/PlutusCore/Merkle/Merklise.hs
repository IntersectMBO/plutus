{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Language.PlutusCore.Merkle.Merklise where



import qualified Codec.Compression.GZip                          as G
import           Codec.Serialise                                 (serialise)
import           Control.Monad
import           Crypto.Hash
import qualified Data.ByteString.Lazy                            as BSL
import           Data.Functor.Foldable
import qualified Data.List
import qualified Data.Map
import qualified Data.Set

import qualified Language.PlutusCore                             as P
import qualified Language.PlutusCore.CBOR                        as P
import qualified Language.PlutusCore.Merkle.CBOR                 as M
import qualified Language.PlutusCore.Merkle.Constant.Typed       as M
import           Language.PlutusCore.Merkle.Convert
import           Language.PlutusCore.Merkle.Evaluation.CekMarker as CekMarker
import qualified Language.PlutusCore.Merkle.Evaluation.Result    as M
import           Language.PlutusCore.Merkle.Merklisable
import qualified Language.PlutusCore.Merkle.PLCSize              as PLCSize
import qualified Language.PlutusCore.Merkle.Size                 as M
import           Language.PlutusCore.Merkle.Type
import qualified Language.PlutusTx.Builtins                      as B

{- Numbering nodes.  We replace the annotations in an AST with unique
   Integers.  We do this by passing in a tree containing all the
   natural numbers, using the number at the root to number the current
   node and left and right subtrees to number subterms etc.  This is a
   bit profligate, but has the advantage of being purely functional. }
-}

type NodeIDs = Data.Set.Set Integer

nodynamics :: M.DynamicBuiltinNameMeanings
nodynamics = M.DynamicBuiltinNameMeanings Data.Map.empty


data Numbers = Numbers {first::Integer, left::Numbers, right:: Numbers}

makeNumbers :: Integer -> Numbers
makeNumbers n = Numbers n (makeNumbers $ 2*n) (makeNumbers $ 2*n+1)

nats :: Numbers
nats = makeNumbers 1
-- An infinite tree containing each integer >= 1 exactly once
-- nats is a bad name.

numberName :: Numbers -> P.Name a -> P.Name Integer
numberName numbers (P.Name x s u) = P.Name (first numbers) s u

numberType :: Numbers -> P.Type P.TyName a -> P.Type P.TyName Integer
numberType (Numbers q l r) =
    \case
      P.TyVar     _ tn      -> P.TyVar     q (numberTyname l tn)
      P.TyFun     _ ty ty'  -> P.TyFun     q (numberType l ty) (numberType r ty')
      P.TyIFix    _ ty ty'  -> P.TyIFix    q (numberType l ty) (numberType r ty')
      P.TyForall  _ tn k ty -> P.TyForall  q (numberTyname (left l) tn) (numberKind (right l) k) (numberType r ty)
      P.TyBuiltin _ tb      -> P.TyBuiltin q tb
      P.TyLam     _ tn k ty -> P.TyLam     q (numberTyname (left l) tn) (numberKind (right l) k) (numberType r ty)
      P.TyApp     _ ty ty'  -> P.TyApp     q (numberType l ty) (numberType r ty')

substConst :: Functor f => t -> f a -> f t
substConst = fmap . const

numberBuiltin :: Numbers -> P.Builtin a -> P.Builtin Integer
numberBuiltin (Numbers q _ _)  = substConst q
-- Maybe I'm trying to be too clever here.  Success depends on the
-- fact that builtins have no subterms, which is invisible in this
-- code.  If we did have subterms, they'd all get the same q.

numberConstant :: Numbers -> P.Constant a -> P.Constant Integer
numberConstant (Numbers q _ _) = substConst q

numberTyname :: Numbers -> P.TyName a -> P.TyName Integer
numberTyname numbers (P.TyName n) = P.TyName (numberName numbers n)

numberKind :: Numbers -> P.Kind a -> P.Kind Integer
numberKind (Numbers q l r) =
    \case
     P.Type _            -> P.Type q
     P.KindArrow _ k1 k2 -> P.KindArrow q (numberKind l k1) (numberKind r k2)

numberTerm :: Numbers -> P.Term P.TyName P.Name a -> P.Term P.TyName P.Name Integer
numberTerm (Numbers q l r) =
    \case
      P.Var      _ n        -> P.Var      q (numberName l n)
      P.LamAbs   _ n ty t   -> P.LamAbs   q (numberName l n) (numberType (left l) ty) (numberTerm r t)
      P.TyInst   _ t ty     -> P.TyInst   q (numberTerm l t) (numberType r ty)
      P.IWrap    _ ty1 ty t -> P.IWrap    q (numberType (left l) ty1) (numberType (right l) ty) (numberTerm l t)
      P.TyAbs    _ tn k t   -> P.TyAbs    q (numberTyname (left l) tn) (numberKind (right l) k) (numberTerm r t)
      P.Apply    _ t1 t2    -> P.Apply    q (numberTerm l t1) (numberTerm r t2)
      P.Unwrap   _ t        -> P.Unwrap   q (numberTerm l t)
      P.Error    _ ty       -> P.Error    q (numberType l ty)
      P.Constant _ c        -> P.Constant q (numberConstant l c)
      P.Builtin  _ b        -> P.Builtin  q (numberBuiltin l b)

numberVersion :: Numbers -> P.Version a -> P.Version Integer
numberVersion (Numbers q _ _) = substConst q

numberProgram :: P.Program P.TyName P.Name a -> P.Program P.TyName P.Name Integer
numberProgram = numProg nats
    where numProg (Numbers q l r) (P.Program _ v t) = P.Program q (numberVersion l v) (numberTerm r t)


{- Pruning unused nodes.  While we're at it, let's convert numeric annotations back to units. -}

unann :: Functor f => f a -> f()
unann x = () <$ x

type NumSet = Data.Set.Set Integer

typeId :: P.Type P.TyName Integer -> Integer
typeId = P.tyLoc

pruneType :: NumSet -> P.Type P.TyName Integer -> Type P.TyName ()
pruneType used ty0 =
    if not $ Data.Set.member (typeId ty0) used
    then TyPruned () (merkleHash (fromCoreType $ unann ty0))
    else case ty0 of
      P.TyVar     _ tn      -> TyVar     () (unann tn)
      P.TyFun     _ ty ty'  -> TyFun     () (pruneType used ty) (pruneType used ty')
      P.TyIFix    _ ty ty'  -> TyIFix    () (pruneType used ty) (pruneType used ty')
      P.TyForall  _ tn k ty -> TyForall  () (unann tn) (unann $ fromCoreKind k) (pruneType used ty)
      P.TyBuiltin _ tb      -> TyBuiltin () tb
      P.TyLam     _ tn k ty -> TyLam     () (unann tn) (unann $ fromCoreKind k) (pruneType used ty)
      P.TyApp     _ ty ty'  -> TyApp     () (pruneType used ty) (pruneType used ty')


termId :: P.Term P.TyName P.Name Integer -> Integer
termId = P.termLoc  -- We should rename termLoc since this isn't a location

pruneTerm :: NumSet -> P.Term P.TyName P.Name Integer -> Term P.TyName P.Name ()
pruneTerm used t0 =
    if not $ Data.Set.member (termId t0) used
    then Prune () (merkleHash (fromCoreTerm $ unann t0))
    else case t0 of
      P.Var      _ n         -> Var      () (unann n)
      P.LamAbs   _ n ty t    -> LamAbs   () (unann n) (pruneType used ty) (pruneTerm used t)
      P.TyInst   _ t ty      -> TyInst   () (pruneTerm used t) (pruneType used ty)
      P.IWrap    _ ty1 ty2 t -> IWrap    () (pruneType used ty1) (pruneType used ty2) (pruneTerm used t)
      P.TyAbs    _ tn k t    -> TyAbs    () (unann tn) (unann $ fromCoreKind k) (pruneTerm used t)
      P.Apply    _ t1 t2     -> Apply    () (pruneTerm used t1) (pruneTerm used t2)
      P.Unwrap   _ t         -> Unwrap   () (pruneTerm used t)
      P.Error    _ ty        -> Error    () (pruneType used ty)
      P.Constant _ c         -> Constant () (unann $ fromCoreConstant c)
      P.Builtin  _ b         -> Builtin  () (unann $ fromCoreBuiltin b)

pruneProgram :: Data.Set.Set Integer -> P.Program P.TyName P.Name Integer -> Program P.TyName P.Name ()
pruneProgram used (P.Program _ v t) = Program () (unann v) (pruneTerm used t)


getUsedNodes :: (Either CekMarker.CekMachineException M.EvaluationResultDef, NodeIDs) -> NodeIDs
getUsedNodes (e, nodes) =
    case e of
     Left _                             -> error "getUsedNodes: Left _"
     Right M.EvaluationFailure          -> error "Evaluation failure in getUsedNodes"
     Right (M.EvaluationSuccess _term ) -> nodes

compress :: B.ByteString -> B.ByteString
compress = G.compressWith G.defaultCompressParams {G.compressLevel = G.bestCompression}

-- TODO: test that if we choose a random node and prune it, the Merkle hash of the AST doesn't change.
merklisationStatistics :: P.Program P.TyName P.Name () -> String
merklisationStatistics program =
    let s1 = serialise program
        numberedProgram = numberProgram program
        P.Program progAnn _ numberedBody = numberedProgram
        bodyAnn = P.termLoc numberedBody
        usedNodes =  getUsedNodes $ CekMarker.evaluateCek nodynamics numberedBody
        prunedProgram = pruneProgram usedNodes numberedProgram
        s2 = serialise prunedProgram
        hash1 = merkleHash $ fromCoreProgram program
        hash2 = merkleHash prunedProgram

        messages = [
         "\nBefore Merklisation",
         " AST size: " ++ (show $ PLCSize.astInfo program),
         " Serialised size = " ++ (show $ BSL.length s1) ++ " bytes",
         " Compressed size = " ++ (show $ BSL.length (compress s1)) ++ " bytes",
         "",
         "After Merklisation",
         " Number of terms used during execution = " ++ (show $ Data.Set.size usedNodes) ,
         "Used nodes: " ++ (show usedNodes),
         "Prog ann = " ++ ( show progAnn),
         "Body ann = " ++ ( show bodyAnn),
         " Remaining nodes: " ++ (show $ M.programSize prunedProgram),
         " AST size: " ++ (show $ M.astInfo prunedProgram),
         " Serialised size = " ++ (show $ BSL.length s2) ++ " bytes",
         " Compressed size = " ++ (show $ BSL.length (compress s2)) ++ " bytes",
         "",
         "Merkle hash before pruning: " ++ (show $ hash1),
         "Merkle hash after  pruning: " ++ (show $ hash2)]
    in Data.List.intercalate "\n" messages


