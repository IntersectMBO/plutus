{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}

-- It is necessary to have Plinth plugin enabled here so that anchors get correctly added.
-- If Plinth plugin is not enabled, profile-all will not be able to correctly retrieve
-- srcspan and in the call trace function call in this module will not have any srcspan
-- information.

module CallTrace.OtherModule where

import PlutusTx.Prelude

errorWhenTrue :: Bool -> BuiltinString
errorWhenTrue True = error ()
errorWhenTrue False = "hi"

wraps :: Bool -> BuiltinString
wraps = errorWhenTrue

class MyClassInOtherModule a where
  myClassFuncInOtherModule :: a -> BuiltinString

instance MyClassInOtherModule Integer where
  myClassFuncInOtherModule n
    | n == 8 = wraps True
    | otherwise = error ()

instance MyClassInOtherModule () where
  myClassFuncInOtherModule () = error ()
