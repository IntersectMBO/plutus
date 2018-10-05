module Language.PlutusCore.TypeSynthesis.Elimination ( ElimCtx (..)
                                                     , elimSubst
                                                     , getElimCtx
                                                     , extractFix
                                                     ) where

import           Language.PlutusCore.Type

data ElimCtx = Hole
             | App ElimCtx (Type TyNameWithKind ())

elimSubst :: ElimCtx -- ^ E
          -> Type TyNameWithKind () -- ^ C
          -> Type TyNameWithKind () -- ^ E{C}
elimSubst Hole ty          = ty
elimSubst (App ctx ty) ty' = TyApp () (elimSubst ctx ty) ty'

getElimCtx :: Type TyNameWithKind () -- ^ E{[(fix a S)/a] S}
           -> ElimCtx -- ^ E
getElimCtx TyApp{} = undefined
getElimCtx _       = Hole -- I think this works because we don't perform reductions ?
-- TODO: also *check* that there are a, S such that E{[fix a S)/a]S} works

-- | Given a type Q, we extract (a, S) such that Q = E{(fix a S)} for some E
extractFix :: Type TyNameWithKind () -- ^ Q = E{(fix a S)}
           -> (TyNameWithKind (), Type TyNameWithKind ()) -- ^ (a, S)
extractFix (TyFix _ tn ty) = (tn, ty)
extractFix (TyApp _ ty _)  = extractFix ty -- can't happen b/c we need ty have to the appropriate kind?
extractFix _               = error "put a real error message here."
