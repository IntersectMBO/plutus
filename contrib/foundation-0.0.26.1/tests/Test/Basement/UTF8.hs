{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE OverloadedStrings   #-}
module Test.Basement.UTF8
    ( tests )
    where

import Basement.Types.CharUTF8
import Foundation
import Foundation.Check
import Foundation.String

tests = Group "utf8"
    [ Property "CharUTF8" $ \c -> decodeCharUTF8 (encodeCharUTF8 c) === c
    ]
