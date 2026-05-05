{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module CallTrace.OtherModule where

import PlutusTx.Prelude

errorWhenTrue :: Bool -> BuiltinString
errorWhenTrue True = error ()
errorWhenTrue False = "hi"
-- NOINLINE ensures that the function appear in the call trace.
{-# NOINLINE errorWhenTrue #-}

wraps :: Bool -> BuiltinString
wraps = errorWhenTrue
-- NOINLINE ensures that the function appear in the call trace.
{-# NOINLINE wraps #-}

class MyClassInOtherModule a where
  myClassFuncInOtherModule :: a -> BuiltinString

instance MyClassInOtherModule Integer where
  myClassFuncInOtherModule n
    | n == 8 = wraps True
    | otherwise = error ()

instance MyClassInOtherModule () where
  myClassFuncInOtherModule () = error ()
