{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.Examples.Data.Shad
    ( shad
    , mkShad
    , recUnit
    , runRecUnit
    ) where

import           PlutusCore.Core
import           PlutusCore.MkPlc
import           PlutusCore.Name
import           PlutusCore.Quote
import           PlutusCore.Universe

-- |
--
-- > getShadF a = \(rec :: * -> *) (i :: *) -> a -> all (a :: * -> *). a i -> integer
getShadF :: uni `Includes` Integer => TyName -> Quote (Type TyName uni ())
getShadF a = do
    rec <- freshTyName "rec"
    i   <- freshTyName "i"
    return
        . TyLam () rec (KindArrow () (Type ()) $ Type ())
        . TyLam () i (Type ())
        . TyFun () (TyVar () a)
        . TyForall () a (KindArrow () (Type ()) $ Type ())
        . TyFun () (TyApp () (TyVar () a) $ TyVar () i)
        $ mkTyBuiltin @Integer ()

-- |
--
-- > \(a :: *) -> ifix (getShadF a) a
shad :: uni `Includes` Integer => Type TyName uni ()
shad = runQuote $ do
    a     <- freshTyName "a"
    shadF <- getShadF a
    return
        . TyLam () a (Type ())
        . TyIFix () shadF
        $ TyVar () a

-- | Test that shadowing does not result in variable capture. The definition is as follows:
--
-- > /\(a :: *) -> wrap (getShadF a) a (\(x : a) -> /\(f :: * -> *) -> \(y : f i) -> 0)
--
-- Type checking this term we eventually reach
--
-- > NORM (vPat (\(a :: k) -> ifix vPat a) arg)
--
-- (where in our case @vPat@ is @shadF@ and @arg@ is @a@), which, if we were naive,
-- would unfold into
--
-- > a -> all (a :: * -> *). a a -> integer
--
-- i.e. we substituted the outer @a@ for @i@, but due to variable capture via @all@ that outer @a@
-- now became an inner one, which would be a bug.
--
-- But that problem is already solved before type checking starts as we rename the program and that
-- makes all binders uniques, so no variable capture is possible due to the outer and inner bindings
-- being distinct.
mkShad :: uni `Includes` Integer => Term TyName Name uni fun ()
mkShad = runQuote $ do
    a     <- freshTyName "a"
    f     <- freshTyName "f"
    shadF <- getShadF a
    x     <- freshName "x"
    y     <- freshName "y"
    return
        . TyAbs () a (Type ())
        . IWrap () shadF (TyVar () a)
        . LamAbs () x (TyVar () a)
        . TyAbs () f (KindArrow () (Type ()) $ Type ())
        . LamAbs () y (TyApp () (TyVar () f) $ TyVar () a)
        $ mkConstant @Integer () 0

-- |
--
-- > recUnitF = \(rec :: * -> *) (i :: *) -> all (r :: *). rec i -> r -> r
recUnitF :: Type TyName uni ()
recUnitF = runQuote $ do
    rec <- freshTyName "rec"
    i   <- freshTyName "i"
    r   <- freshTyName "r"
    return
        . TyLam () rec (KindArrow () (Type ()) $ Type ())
        . TyLam () i (Type ())
        . TyForall () r (Type ())
        . TyFun () (TyApp () (TyVar () rec) $ TyVar () i)
        . TyFun () (TyVar () r)
        $ TyVar () r

-- |
--
-- > ifix recUnitF ()
recUnit :: uni `Includes` () => Type TyName uni ()
recUnit = TyIFix () recUnitF $ mkTyBuiltin @() ()

-- |  Test that a binder in a pattern functor does not get duplicated. The definition is as follows:
--
-- > /\(a :: *) -> \(ru : recUnit) -> unwrap ru {a} ru
--
-- Type checking this term we eventually reach
--
-- > NORM (vPat (\(a :: k) -> ifix vPat a) arg)
--
-- (where in our case @vPat@ is @recUnitF@ and @arg@ is @()@), which, if we were naive,
-- would unfold into
--
-- > all (r :: *). ifix (\(rec :: * -> *) (i :: *) -> all (r :: *). rec i -> r -> r) () -> r -> r
--
-- and break global uniqueness as the @all (r :: *)@ binder appears twice.
--
-- But this doesn't happen in the actual code, since when a variable gets looked up during type
-- normalization, its value gets renamed, which means that a fresh variable will be generated for
-- the inner binder and there will be no shadowing.
runRecUnit :: uni `Includes` () => Term TyName Name uni fun ()
runRecUnit = runQuote $ do
    a  <- freshTyName "a"
    ru <- freshName "ru"
    return
        . TyAbs () a (Type ())
        . LamAbs () ru recUnit
        . Apply () (TyInst () (Unwrap () $ Var () ru) $ TyVar () a)
        $ Var () ru
