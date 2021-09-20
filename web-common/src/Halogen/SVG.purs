module Halogen.SVG where

import Prelude
import DOM.HTML.Indexed (Interactive)
import Data.Array as Array
import Data.Newtype (unwrap)
import Data.String (joinWith)
import Halogen.HTML (AttrName(..), ClassName, ElemName(..), HTML, Namespace(..), Node, elementNS, text)
import Halogen.HTML as HH
import Halogen.HTML.Properties (CSSPixel, IProp)

------------------------------------------------------------
-- Nodes.
------------------------------------------------------------
type SVGNode
  = SVGStyling
      ( SVGCore
          ( viewBox :: Box
          , xmlns :: Namespace
          , width :: Length
          , height :: Length
          , class :: String
          , role :: String
          )
      )

type SVGrect
  = SVGPresentation
      ( Interactive
          ( x :: CSSPixel
          , y :: CSSPixel
          , width :: Length
          , height :: Length
          , fill :: RGB
          , stroke :: RGB
          , strokeWidth :: CSSPixel
          )
      )

type SVGg
  = SVGPresentation (SVGCore ())

type SVGCore r
  = ( id :: String, class :: String | r )

type SVGStyling r
  = ( style :: String | r )

type SVGPresentation r
  = ( transform :: Translate | r )

type SVGline
  = ( x1 :: Length
    , y1 :: Length
    , x2 :: Length
    , y2 :: Length
    , stroke :: RGB
    , strokeWidth :: CSSPixel
    )

type SVGtext
  = SVGPresentation
      ( x :: CSSPixel
      , y :: CSSPixel
      , stroke :: RGB
      , textAnchor :: Anchor
      , transform :: Translate
      )

type SVGgradiant
  = ( id :: String
    , x1 :: Length
    , x2 :: Length
    , y1 :: Length
    , y2 :: Length
    , gradientUnits :: GradientUnits
    )

type SVGstop
  = ( offset :: Length
    , stopColour :: String
    )

type SVGcircle
  = SVGCore
      ( id :: String
      , fill :: RGB
      , strokeWidth :: CSSPixel
      , strokeLinecap :: Linecap
      , cx :: Length
      , cy :: Length
      , r :: Length
      )

type SVGpath
  = ( id :: String
    , d :: String
    , transform :: Translate
    , fill :: RGB
    )

type SVGUse
  = ( xmlns :: Namespace
    , xlink :: String
    )

svgNS :: Namespace
svgNS = Namespace "http://www.w3.org/2000/svg"

xlinkNS :: Namespace
xlinkNS = Namespace "http://www.w3.org/2000/svg"

svg :: forall p i. Node SVGNode p i
svg attributes = elementNS svgNS (ElemName "svg") (Array.snoc attributes (xmlns svgNS))

defs :: forall r p i. Node r p i
defs = elementNS svgNS (ElemName "defs")

linearGradient :: forall p i. Node SVGgradiant p i
linearGradient = elementNS svgNS (ElemName "linearGradient")

stop :: forall p i. Node SVGstop p i
stop = elementNS svgNS (ElemName "stop")

path :: forall p i. Node SVGpath p i
path = elementNS svgNS (ElemName "path")

circle :: forall p i. Node SVGcircle p i
circle = elementNS svgNS (ElemName "circle")

rect :: forall p i. Node SVGrect p i
rect = elementNS svgNS (ElemName "rect")

svgText :: forall r i. Array (IProp SVGtext i) -> String -> HTML r i
svgText attributes content = elementNS svgNS (ElemName "text") attributes [ text content ]

g :: forall p i. Node SVGg p i
g = elementNS svgNS (ElemName "g")

line :: forall p i. Node SVGline p i
line = elementNS svgNS (ElemName "line")

use :: forall p i. Namespace -> Node SVGUse p i
use ns = elementNS ns (ElemName "use")

------------------------------------------------------------
-- Attributes.
------------------------------------------------------------
class IsAttr a where
  toAttrValue :: a -> String

instance isAttrNamespace :: IsAttr Namespace where
  toAttrValue (Namespace namespace) = namespace

instance isAttrString :: IsAttr String where
  toAttrValue = identity

instance isAttrInt :: IsAttr Int where
  toAttrValue = show

attr :: forall i r a. IsAttr a => AttrName -> a -> IProp r i
attr name = HH.attr name <<< toAttrValue

x :: forall r i. CSSPixel -> IProp ( x :: CSSPixel | r ) i
x = attr (AttrName "x")

y :: forall r i. CSSPixel -> IProp ( y :: CSSPixel | r ) i
y = attr (AttrName "y")

x1 :: forall r i. Length -> IProp ( x1 :: Length | r ) i
x1 = attr (AttrName "x1")

y1 :: forall r i. Length -> IProp ( y1 :: Length | r ) i
y1 = attr (AttrName "y1")

x2 :: forall r i. Length -> IProp ( x2 :: Length | r ) i
x2 = attr (AttrName "x2")

y2 :: forall r i. Length -> IProp ( y2 :: Length | r ) i
y2 = attr (AttrName "y2")

cx :: forall r i. Length -> IProp ( cx :: Length | r ) i
cx = attr (AttrName "cx")

cy :: forall r i. Length -> IProp ( cy :: Length | r ) i
cy = attr (AttrName "cy")

r :: forall r i. Length -> IProp ( r :: Length | r ) i
r = attr (AttrName "r")

-- | `AttrName "className"` as used by Halogen.HTML.Properties does not work with SVG
-- | See https://github.com/niklasvh/html2canvas/pull/2034
clazz :: forall r i. ClassName -> IProp ( class :: String | r ) i
clazz = unwrap >>> attr (AttrName "class")

height :: forall r i. Length -> IProp ( height :: Length | r ) i
height = attr (AttrName "height")

width :: forall r i. Length -> IProp ( width :: Length | r ) i
width = attr (AttrName "width")

gradientUnits :: forall r i. GradientUnits -> IProp ( gradientUnits :: GradientUnits | r ) i
gradientUnits = attr (AttrName "gradientUnits")

offset :: forall r i. Length -> IProp ( offset :: Length | r ) i
offset = attr (AttrName "offset")

stopColour :: forall r i. String -> IProp ( stopColour :: String | r ) i
stopColour = attr (AttrName "stop-color")

xmlns :: forall r i. Namespace -> IProp ( xmlns :: Namespace | r ) i
xmlns = attr (AttrName "xmlns")

d :: forall r i. String -> IProp ( d :: String | r ) i
d = attr (AttrName "d")

transform :: forall r i. Translate -> IProp ( transform :: Translate | r ) i
transform = attr (AttrName "transform")

textAnchor :: forall r i. Anchor -> IProp ( textAnchor :: Anchor | r ) i
textAnchor = attr (AttrName "text-anchor")

fill :: forall r i. RGB -> IProp ( fill :: RGB | r ) i
fill = attr (AttrName "fill")

stroke :: forall r i. RGB -> IProp ( stroke :: RGB | r ) i
stroke = attr (AttrName "stroke")

strokeWidth :: forall r i. CSSPixel -> IProp ( strokeWidth :: CSSPixel | r ) i
strokeWidth = attr (AttrName "stroke-width")

strokeLinecap :: forall r i. Linecap -> IProp ( strokeLinecap :: Linecap | r ) i
strokeLinecap = attr (AttrName "stroke-linecap")

id_ :: forall r i. String -> IProp ( id :: String | r ) i
id_ = attr (AttrName "id")

style :: forall r i. String -> IProp ( style :: String | r ) i
style = attr (AttrName "style")

viewBox :: forall i r. Box -> IProp ( viewBox :: Box | r ) i
viewBox = attr (AttrName "viewBox")

xlink :: forall i r. String -> IProp ( xlink :: String | r ) i
xlink = attr (AttrName "xlink:href")

------------------------------------------------------------
-- Types
------------------------------------------------------------
data Box
  = Box
    { x :: Int
    , y :: Int
    , width :: Int
    , height :: Int
    }

instance isAttrBox :: IsAttr Box where
  toAttrValue (Box box) = joinWith " " (show <$> [ box.x, box.y, box.width, box.height ])

data Translate
  = Translate
    { x :: Number
    , y :: Number
    }

instance isAttrTranslate :: IsAttr Translate where
  toAttrValue (Translate translate) = "translate" <> parens (joinWith "," (show <$> [ translate.x, translate.y ]))

data RGB
  = RGB
    { red :: Int
    , green :: Int
    , blue :: Int
    }
  | Hex String
  | None

instance isAttrRGB :: IsAttr RGB where
  toAttrValue (RGB { red, green, blue }) = "rgb" <> parens (joinWith "," (show <$> [ red, green, blue ]))
  toAttrValue (Hex val) = val
  toAttrValue None = "none"

toRGB :: Int -> Int -> Int -> RGB
toRGB red green blue = RGB { red, green, blue }

data Anchor
  = Start
  | Middle
  | End

instance isAttrAnchor :: IsAttr Anchor where
  toAttrValue Start = "start"
  toAttrValue Middle = "middle"
  toAttrValue End = "end"

parens :: String -> String
parens str = "(" <> str <> ")"

data GradientUnits
  = UserSpaceOnUse
  | ObjectBoundingBox

instance isAttrGradientUnits :: IsAttr GradientUnits where
  toAttrValue UserSpaceOnUse = "userSpaceOnUse"
  toAttrValue ObjectBoundingBox = "objectBoundingBox"

data Length
  = Length Number
  | Px Int

instance isAttrLength :: IsAttr Length where
  toAttrValue (Length n) = show n
  toAttrValue (Px n) = show n <> "px"

data Linecap
  = Round

instance isAttrLinecap :: IsAttr Linecap where
  toAttrValue Round = "round"
