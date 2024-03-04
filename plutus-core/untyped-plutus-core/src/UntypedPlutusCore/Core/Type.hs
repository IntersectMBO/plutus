-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module UntypedPlutusCore.Core.Type
    ( TPLC.UniOf
    , TPLC.Version (..)
    , TPLC.Binder (..)
    , Term (..)
    , Program (..)
    , SixList (..)
    , lookupSixList
    , progAnn
    , progVer
    , progTerm
    , bindFunM
    , bindFun
    , mapFun
    , termAnn
    , UVarDecl(..)
    , uvarDeclName
    , uvarDeclAnn
    ) where

import Control.Lens
import PlutusPrelude

import Data.Hashable
import Data.Word
import GHC.Exts as Exts (IsList (..), inline)
import PlutusCore.Builtin qualified as TPLC
import PlutusCore.Core qualified as TPLC
import PlutusCore.MkPlc
import PlutusCore.Name qualified as TPLC
import Universe

{- Note [Term constructor ordering and numbers]
Ordering of constructors has a small but real effect on efficiency.
It's slightly more efficient to hit the earlier constructors, so it's better to put the more
common ones first.

The current ordering is based on their *empirically observed* frequency. We should check this
occasionally.

Additionally, the first 7 (or 3 on 32-bit systems) constructors will get *pointer tags*, which allows
more efficient access when casing on them. So we ideally want to keep the number of constructors
at 7 or fewer.

We've got 8 constructors, *but* the last one is Error, which is only going to be seen at most
once per program, so it's not too big a deal if it doesn't get a tag.

See the GHC Notes "Tagging big families" and "Double switching for big families" in
GHC.StgToCmm.Expr for more details.
-}

{-| The type of Untyped Plutus Core terms. Mirrors the type of Typed Plutus Core terms except

1. all types are removed
2. 'IWrap' and 'Unwrap' are removed
3. type abstractions are replaced with 'Delay'
4. type instantiations are replaced with 'Force'

The latter two are due to the fact that we don't have value restriction in Typed Plutus Core
and hence a computation can be stuck expecting only a single type argument for the computation
to become unstuck. Therefore we can't just silently remove type abstractions and instantiations and
need to replace them with something else that also blocks evaluation (in order for the semantics
of an erased program to match with the semantics of the original typed one). 'Delay' and 'Force'
serve exactly this purpose.
-}
-- Making all the fields strict gives us a couple of percent in benchmarks
-- See Note [Term constructor ordering and numbers]
data Term name uni fun ann
    = Var !ann !name
    | LamAbs !ann !name !(Term name uni fun ann)
    | Apply !ann !(Term name uni fun ann) !(Term name uni fun ann)
    | Force !ann !(Term name uni fun ann)
    | Delay !ann !(Term name uni fun ann)
    | Constant !ann !(Some (ValueOf uni))
    | Builtin !ann !fun
    -- This is the cutoff at which constructors won't get pointer tags
    -- See Note [Term constructor ordering and numbers]
    | Error !ann
    -- TODO: worry about overflow, maybe use an Integer
    -- TODO: try spine-strict list or strict list or vector
    -- See Note [Constr tag type]
    | Constr !ann !Word64 ![Term name uni fun ann]
    | Case !ann !(Term name uni fun ann) !(SixList (Term name uni fun ann))
    deriving stock (Functor, Generic)

data SixList a
    = SixList0
    | SixList1  !a
    | SixList2  !a !a
    | SixList3  !a !a !a
    | SixList4  !a !a !a !a
    | SixList5  !a !a !a !a !a
    | SixList6  !a !a !a !a !a !a
    | SixList7  !a !a !a !a !a !a !a
    | SixList8  !a !a !a !a !a !a !a !a
    | SixList9  !a !a !a !a !a !a !a !a !a
    | SixList10 !a !a !a !a !a !a !a !a !a !a
    | SixList11 !a !a !a !a !a !a !a !a !a !a !a
    | SixList12 !a !a !a !a !a !a !a !a !a !a !a !a
    | SixList13 !a !a !a !a !a !a !a !a !a !a !a !a !a
    | SixList14 !a !a !a !a !a !a !a !a !a !a !a !a !a !a (SixList a)
    deriving stock (Show, Eq, Functor, Foldable, Traversable, Generic)
    deriving anyclass (NFData, Hashable)

instance IsList (SixList a) where
    type Item (SixList a) = a

    fromList []                                   = SixList0
    fromList [x0]                                 = SixList1 x0
    fromList [x0, x1]                             = SixList2 x0 x1
    fromList [x0, x1, x2]                         = SixList3 x0 x1 x2
    fromList [x0, x1, x2, x3]                     = SixList4 x0 x1 x2 x3
    fromList [x0, x1, x2, x3, x4]                 = SixList5 x0 x1 x2 x3 x4
    fromList [x0, x1, x2, x3, x4, x5]             = SixList6 x0 x1 x2 x3 x4 x5
    fromList [x0, x1, x2, x3, x4, x5, x6]         = SixList7 x0 x1 x2 x3 x4 x5 x6
    fromList [x0, x1, x2, x3, x4, x5, x6, x7]     = SixList8 x0 x1 x2 x3 x4 x5 x6 x7
    fromList [x0, x1, x2, x3, x4, x5, x6, x7, x8] = SixList9 x0 x1 x2 x3 x4 x5 x6 x7 x8
    fromList [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] = SixList10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    fromList [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10] = SixList11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    fromList [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] = SixList12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    fromList [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] = SixList13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    fromList (x0:x1:x2:x3:x4:x5:x6:x7:x8:x9:x10:x11:x12:x13:xs) = SixList14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 (fromList xs)

    toList !xs0 = goStep xs0 where
        goStep :: SixList a -> [a]
        goStep SixList0                        = []
        goStep (SixList1 x0)                   = [x0]
        goStep (SixList2 x0 x1)                = [x0, x1]
        goStep (SixList3 x0 x1 x2)             = [x0, x1, x2]
        goStep (SixList4 x0 x1 x2 x3)          = [x0, x1, x2, x3]
        goStep (SixList5 x0 x1 x2 x3 x4)       = [x0, x1, x2, x3, x4]
        goStep (SixList6 x0 x1 x2 x3 x4 x5)    = [x0, x1, x2, x3, x4, x5]
        goStep (SixList7 x0 x1 x2 x3 x4 x5 x6) = [x0, x1, x2, x3, x4, x5, x6]
        goStep (SixList8 x0 x1 x2 x3 x4 x5 x6 x7) = [x0, x1, x2, x3, x4, x5, x6, x7]
        goStep (SixList9 x0 x1 x2 x3 x4 x5 x6 x7 x8) = [x0, x1, x2, x3, x4, x5, x6, x7, x8]
        goStep (SixList10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9]
        goStep (SixList11 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10]
        goStep (SixList12 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]
        goStep (SixList13 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12]
        goStep (SixList14 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 xs) = x0 : x1 : x2 : x3 : x4 : x5 : x6 : x7 : x8 : x9 : x10 : x11 : x12 : x13 : goRec xs
        {-# INLINE goStep #-}

        goRec :: SixList a -> [a]
        goRec !xs = goStep xs
        {-# NOINLINE goRec #-}
    {-# INLINE toList #-}

-- >>> import GHC.IsList (fromList)
-- >>> import Data.Maybe
-- >>> mapMaybe (\i -> lookupSixList i $ fromList [0..20 :: Int]) [0..20]
-- [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
lookupSixList :: Word64 -> SixList a -> Maybe a
lookupSixList !i0 = goStep i0 . inline Exts.toList where
    goStep :: Word64 -> [a] -> Maybe a
    goStep 0 = \case
        x:_ -> Just x
        _   -> Nothing
    goStep 1 = \case
        _:x:_ -> Just x
        _     -> Nothing
    goStep 2 = \case
        _:_:x:_ -> Just x
        _       -> Nothing
    goStep 3 = \case
        _:_:_:x:_ -> Just x
        _         -> Nothing
    goStep 4 = \case
        _:_:_:_:x:_ -> Just x
        _           -> Nothing
    goStep 5 = \case
        _:_:_:_:_:x:_ -> Just x
        _             -> Nothing
    goStep 6 = \case
        _:_:_:_:_:_:x:_ -> Just x
        _               -> Nothing
    goStep 7 = \case
        _:_:_:_:_:_:_:x:_ -> Just x
        _                 -> Nothing
    goStep 8 = \case
        _:_:_:_:_:_:_:_:x:_ -> Just x
        _                   -> Nothing
    goStep 9 = \case
        _:_:_:_:_:_:_:_:_:x:_ -> Just x
        _                     -> Nothing
    goStep 10 = \case
        _:_:_:_:_:_:_:_:_:_:x:_ -> Just x
        _                       -> Nothing
    goStep 11 = \case
        _:_:_:_:_:_:_:_:_:_:_:x:_ -> Just x
        _                         -> Nothing
    goStep 12 = \case
        _:_:_:_:_:_:_:_:_:_:_:_:x:_ -> Just x
        _                           -> Nothing
    goStep 13 = \case
        _:_:_:_:_:_:_:_:_:_:_:_:_:x:_ -> Just x
        _                             -> Nothing
    goStep i = \case
        _:_:_:_:_:_:_:_:_:_:_:_:_:_:xs -> goRec (i - 14) xs
        _                              -> Nothing
    {-# INLINE goStep #-}

    goRec :: Word64 -> [a] -> Maybe a
    goRec !i = goStep i
    {-# NOINLINE goRec #-}
{-# INLINE lookupSixList #-}

deriving stock instance (Show name, GShow uni, Everywhere uni Show, Show fun, Show ann, Closed uni)
    => Show (Term name uni fun ann)

deriving anyclass instance (NFData name, NFData fun, NFData ann, Everywhere uni NFData, Closed uni)
    => NFData (Term name uni fun ann)

-- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
data Program name uni fun ann = Program
    { _progAnn  :: ann
    , _progVer  :: TPLC.Version
    , _progTerm :: Term name uni fun ann
    }
    deriving stock (Functor, Generic)
makeLenses ''Program

deriving stock instance (Show name, GShow uni, Everywhere uni Show, Show fun, Show ann, Closed uni)
    => Show (Program name uni fun ann)

deriving anyclass instance (NFData name, Everywhere uni NFData, NFData fun, NFData ann, Closed uni)
    => NFData (Program name uni fun ann)

type instance TPLC.UniOf (Term name uni fun ann) = uni

instance TermLike (Term name uni fun) TPLC.TyName name uni fun where
    var      = Var
    tyAbs    = \ann _ _ -> Delay ann
    lamAbs   = \ann name _ -> LamAbs ann name
    apply    = Apply
    constant = Constant
    builtin  = Builtin
    tyInst   = \ann term _ -> Force ann term
    unwrap   = const id
    iWrap    = \_ _ _ -> id
    error    = \ann _ -> Error ann
    constr   = \ann _ i es -> Constr ann i es
    kase     = \ann _ arg cs -> Case ann arg $ fromList cs

instance TPLC.HasConstant (Term name uni fun ()) where
    asConstant (Constant _ val) = pure val
    asConstant _                = TPLC.throwNotAConstant

    fromConstant = Constant ()

type instance TPLC.HasUniques (Term name uni fun ann) = TPLC.HasUnique name TPLC.TermUnique
type instance TPLC.HasUniques (Program name uni fun ann) = TPLC.HasUniques (Term name uni fun ann)

-- | An untyped "variable declaration", i.e. a name for a variable.
data UVarDecl name ann = UVarDecl
    { _uvarDeclAnn  :: ann
    , _uvarDeclName :: name
    } deriving stock (Functor, Show, Generic)
makeLenses ''UVarDecl

-- | Return the outermost annotation of a 'Term'.
termAnn :: Term name uni fun ann -> ann
termAnn (Constant ann _) = ann
termAnn (Builtin ann _)  = ann
termAnn (Var ann _)      = ann
termAnn (LamAbs ann _ _) = ann
termAnn (Apply ann _ _)  = ann
termAnn (Delay ann _)    = ann
termAnn (Force ann _)    = ann
termAnn (Error ann)      = ann
termAnn (Constr ann _ _) = ann
termAnn (Case ann _ _)   = ann

bindFunM
    :: Monad m
    => (ann -> fun -> m (Term name uni fun' ann))
    -> Term name uni fun ann
    -> m (Term name uni fun' ann)
bindFunM f = go where
    go (Constant ann val)     = pure $ Constant ann val
    go (Builtin ann fun)      = f ann fun
    go (Var ann name)         = pure $ Var ann name
    go (LamAbs ann name body) = LamAbs ann name <$> go body
    go (Apply ann fun arg)    = Apply ann <$> go fun <*> go arg
    go (Delay ann term)       = Delay ann <$> go term
    go (Force ann term)       = Force ann <$> go term
    go (Error ann)            = pure $ Error ann
    go (Constr ann i args)    = Constr ann i <$> traverse go args
    go (Case ann arg cs)      = Case ann <$> go arg <*> traverse go cs

bindFun
    :: (ann -> fun -> Term name uni fun' ann)
    -> Term name uni fun ann
    -> Term name uni fun' ann
bindFun f = runIdentity . bindFunM (coerce f)

mapFun :: (ann -> fun -> fun') -> Term name uni fun ann -> Term name uni fun' ann
mapFun f = bindFun $ \ann fun -> Builtin ann (f ann fun)
