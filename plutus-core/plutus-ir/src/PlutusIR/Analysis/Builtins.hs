{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
module PlutusIR.Analysis.Builtins
    ( BuiltinMatcherLike (..)
    , bmlSplitMatchContext
    , bmlBranchArities
    , defaultUniMatcherLike
    , BuiltinsInfo (..)
    , biSemanticsVariant
    , biMatcherLike
    , builtinArityInfo
    , asBuiltinDatatypeMatch
    , builtinDatatypeMatchBranchArities
    ) where

import Control.Lens hiding (parts)
import Data.Functor (void)
import Data.Kind
import Data.Map qualified as Map
import Data.Proxy
import PlutusCore.Arity
import PlutusCore.Builtin
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Default
import PlutusCore.MkPlc (mkIterTyAppNoAnn)
import PlutusIR.Contexts
import PlutusPrelude (Default (..))

-- | The information we need to work with a builtin that is like a datatype matcher.
data BuiltinMatcherLike uni fun = BuiltinMatcherLike
  { _bmlSplitMatchContext :: forall tyname name a .
    Prism' (AppContext tyname name uni fun a) (SplitMatchContext tyname name uni fun a)
  , _bmlBranchArities :: [Arity]
  }
makeLenses ''BuiltinMatcherLike

-- | All non-static information about builtins that the compiler might want.
data BuiltinsInfo (uni :: Type -> Type) fun = BuiltinsInfo
  { _biSemanticsVariant :: PLC.BuiltinSemanticsVariant fun
  , _biMatcherLike      :: Map.Map fun (BuiltinMatcherLike uni fun)
  }
makeLenses ''BuiltinsInfo

instance Default (BuiltinsInfo DefaultUni DefaultFun) where
  def = BuiltinsInfo
        { _biSemanticsVariant = def
        , _biMatcherLike = defaultUniMatcherLike
        }

-- | Get the arity of a builtin function from the 'PLC.BuiltinInfo'.
builtinArityInfo
    :: forall uni fun
    . ToBuiltinMeaning uni fun
    => BuiltinsInfo uni fun
    -> fun
    -> Arity
builtinArityInfo binfo = builtinArity (Proxy @uni) (binfo ^. biSemanticsVariant)

-- | Split a builtin 'match'.
asBuiltinDatatypeMatch ::
  Ord fun
  => BuiltinsInfo uni fun
  -> fun
  -> Maybe (APrism' (AppContext tyname name uni fun a) (SplitMatchContext tyname name uni fun a))
asBuiltinDatatypeMatch binfo f
  | Just (BuiltinMatcherLike p _) <- Map.lookup f (binfo ^. biMatcherLike)
  = Just p
  | otherwise = Nothing

-- | Get the branch arities for a builtin 'match'.
builtinDatatypeMatchBranchArities ::
  Ord fun
  => BuiltinsInfo uni fun
  -> fun
  -> Maybe [Arity]
builtinDatatypeMatchBranchArities binfo f
  | Just (BuiltinMatcherLike _ arities) <- Map.lookup f (binfo ^. biMatcherLike)
  = Just arities
  | otherwise = Nothing

defaultUniMatcherLike :: Map.Map DefaultFun (BuiltinMatcherLike DefaultUni DefaultFun)
defaultUniMatcherLike = Map.fromList
  [ (IfThenElse,
     BuiltinMatcherLike (prism' reconstructIfThenElse splitIfThenElse) ifThenElseBranchArities)
  , (ChooseUnit,
     BuiltinMatcherLike (prism' reconstructChooseUnit splitChooseUnit) chooseUnitBranchArities)
  , (ChooseList,
     BuiltinMatcherLike (prism' reconstructChooseList splitChooseList) chooseListBranchArities)
  ]
  where
    splitIfThenElse
      :: AppContext tyname name DefaultUni DefaultFun a
      -> Maybe (SplitMatchContext tyname name DefaultUni DefaultFun a)
    splitIfThenElse args
      -- Okay to use the default semantics variant here as we're assuming the
      -- type never changes
      | Just Saturated <- saturates args (builtinArity Proxy def IfThenElse)
      -- 1. No ty vars
      -- 2. Result type comes first
      -- 3. Scrutinee next
      -- 4. Then branches
      , (TypeAppContext resTy resTyAnn (TermAppContext scrut scrutAnn branches)) <- args
      =
        let
          scrutTy = mkTyBuiltin @_ @Bool ()
          sm = SplitMatchContext mempty (scrut, scrutTy, scrutAnn) (resTy, resTyAnn) branches
        in Just sm
      | otherwise = Nothing
    reconstructIfThenElse (SplitMatchContext _ (scrut, _, scrutAnn) (resTy, resTyAnn) branches) =
      TypeAppContext resTy resTyAnn (TermAppContext scrut scrutAnn branches)
    -- both branches have no args
    ifThenElseBranchArities = [[], []]

    splitChooseUnit
      :: AppContext tyname name DefaultUni DefaultFun a
      -> Maybe (SplitMatchContext tyname name DefaultUni DefaultFun a)
    splitChooseUnit args
      -- Okay to use the default semantics variant here as we're assuming the
      -- type never changes
      | Just Saturated <- saturates args (builtinArity Proxy def ChooseUnit)
      -- 1. No ty vars
      -- 2. Result type comes first
      -- 3. Scrutinee next
      -- 4. Then branches
      , (TypeAppContext resTy resTyAnn (TermAppContext scrut scrutAnn branches)) <- args
      =
        let
          scrutTy = mkTyBuiltin @_ @() ()
          sm = SplitMatchContext mempty (scrut, scrutTy, scrutAnn) (resTy, resTyAnn) branches
        in Just sm
      | otherwise = Nothing
    reconstructChooseUnit (SplitMatchContext _ (scrut, _, scrutAnn) (resTy, resTyAnn) branches) =
      TypeAppContext resTy resTyAnn (TermAppContext scrut scrutAnn branches)
    -- only branch has no args
    chooseUnitBranchArities = [[]]

    splitChooseList
      :: AppContext tyname name DefaultUni DefaultFun a
      -> Maybe (SplitMatchContext tyname name DefaultUni DefaultFun a)
    splitChooseList args
      -- Okay to use the default semantics variant here as we're assuming the
      -- type never changes
      | Just Saturated <- saturates args (builtinArity Proxy def ChooseList)
      -- 1. One type variable
      -- 2. Then the result type
      -- 3. Scrutinee next
      -- 4. Then branches
      , (vars, TypeAppContext resTy resTyAnn (TermAppContext scrut scrutAnn branches)) <-
        splitAppContext 1 args
      = do
          tyArgs <- extractTyArgs vars
          let scrutTy = mkIterTyAppNoAnn (mkTyBuiltin @_ @[] ()) (fmap void tyArgs)
              sm = SplitMatchContext vars (scrut, scrutTy, scrutAnn) (resTy, resTyAnn) branches
          pure sm
      | otherwise = Nothing
    reconstructChooseList (SplitMatchContext vars (scrut, _, scrutAnn) (resTy, resTyAnn) branches) =
      vars <> TypeAppContext resTy resTyAnn (TermAppContext scrut scrutAnn branches)
    -- both branches have no args
    chooseListBranchArities = [[], []]
