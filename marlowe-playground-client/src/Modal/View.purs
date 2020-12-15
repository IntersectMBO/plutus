module Modal.View
  ( modal
  ) where

import Data.Lens ((^.))
import Data.Maybe (Maybe(..))
import Demos.View (render) as Demos
import Effect.Aff.Class (class MonadAff)
import GistButtons (authButton)
import Halogen (ComponentHTML)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (ClassName(ClassName), div, text)
import Halogen.HTML.Properties (classes)
import MainFrame.Types (Action(..), ChildSlots, ModalView(..), State, _newProject, _projects, _rename, _saveAs, _showModal)
import NewProject.View (render) as NewProject
import Prelude (identity)
import Projects.View (render) as Projects
import Rename.State (render) as Rename
import SaveAs.State (render) as SaveAs
import ConfirmUnsavedNavigation.View (render) as ConfirmUnsavedNavigation

modal ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
modal state = case state ^. _showModal of
  Nothing -> text ""
  Just view ->
    div [ classes [ ClassName "overlay" ] ]
      [ div [ classes [ ClassName "modal" ] ]
          [ modalContent view ]
      ]
  where
  modalContent = case _ of
    NewProject -> renderSubmodule _newProject NewProjectAction NewProject.render state
    OpenProject -> renderSubmodule _projects ProjectsAction Projects.render state
    OpenDemo -> renderSubmodule identity DemosAction Demos.render state
    RenameProject -> renderSubmodule _rename RenameAction Rename.render state
    SaveProjectAs -> renderSubmodule _saveAs SaveAsAction SaveAs.render state
    (ConfirmUnsavedNavigation intendedAction) -> ConfirmUnsavedNavigation.render intendedAction state
    (GithubLogin intendedAction) -> authButton intendedAction state
