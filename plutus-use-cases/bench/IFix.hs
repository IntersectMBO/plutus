{-# LANGUAGE GADTs #-}
module IFix where

data IFix f a where
    Wrap :: f (IFix f) a -> IFix f a
