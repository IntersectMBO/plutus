{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module CallTrace.OtherModule where

import PlutusTx.Prelude

errorWhenTrue :: Bool -> BuiltinString
errorWhenTrue True  = error ()
errorWhenTrue False = "hi"

wraps :: Bool -> BuiltinString
wraps = errorWhenTrue

class MyClassInOtherModule a where
  myClassFuncInOtherModule :: a -> BuiltinString

instance MyClassInOtherModule Integer where
  myClassFuncInOtherModule x
          -- no case on integer here, because our compiler cannot manage it
          | x == 8 = wraps True
          | otherwise = error ()

instance MyClassInOtherModule () where
  myClassFuncInOtherModule () =  error ()
