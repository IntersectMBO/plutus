{-# LANGUAGE OverloadedStrings #-}

module Common where

import Brick.AttrMap qualified as B
import Brick.Types qualified as B
import Brick.Widgets.Center qualified as BC
import Brick.Widgets.Core qualified as B
import Data.Text (Text)

menuAttr :: B.AttrName
menuAttr = B.attrName "menu"

highlightAttr :: B.AttrName
highlightAttr = B.attrName "highlight"

header :: Text -> B.Widget a -> B.Widget a
header title =
    (B.vLimit 1 (B.withAttr menuAttr . BC.hCenter $ B.txt title) B.<=>)

footer :: forall a. B.Widget a
footer =
    B.padTop (B.Pad 1) . BC.hCenter . B.withAttr menuAttr $
        B.txt "(?): Key Bindings"
