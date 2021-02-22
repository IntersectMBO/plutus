module BlocklyComponent.View where

import Prelude hiding (div)
import Data.Maybe (Maybe(..))
import Halogen (ClassName(..), RefLabel(..))
import Halogen.Classes (fullHeight, fullWidth)
import Halogen.HTML (HTML, div, text)
import Halogen.HTML.Properties (class_, classes, id_, ref)

blocklyRef :: RefLabel
blocklyRef = RefLabel "blockly"

render :: forall r p action. { errorMessage :: Maybe String | r } -> HTML p action
render state =
  div
    [ ref blocklyRef
    , id_ "blocklyWorkspace"
    , classes [ fullHeight, fullWidth ]
    ]
    [ errorMessage state.errorMessage ]

errorMessage :: forall p i. Maybe String -> HTML p i
errorMessage (Just error) = div [ class_ (ClassName "blocklyError") ] [ text error ]

errorMessage Nothing = div [ class_ (ClassName "blocklyError") ] []
