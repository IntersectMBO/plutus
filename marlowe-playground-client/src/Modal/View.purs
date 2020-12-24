module Modal.View
  ( modal
  ) where

import ConfirmUnsavedNavigation.View (render) as ConfirmUnsavedNavigation
import Data.Lens ((^.))
import Data.Maybe (Maybe(..))
import Demos.View (render) as Demos
import Effect.Aff.Class (class MonadAff)
import GistButtons (authButton)
import Halogen (ComponentHTML)
import Halogen.Extra (renderSubmodule)
import Halogen.HTML (ClassName(ClassName), div, text)
import Halogen.HTML.Properties (classes)
import MainFrame.Types (Action(..), ChildSlots, ModalView(..), State, _newProject, _projects, _rename, _saveAs, _showModal, hasGlobalLoading)
import NewProject.View (render) as NewProject
import Prelude (identity)
import Projects.View (render) as Projects
import Rename.State (render) as Rename
import SaveAs.State (render) as SaveAs

modal ::
  forall m.
  MonadAff m =>
  State ->
  ComponentHTML Action ChildSlots m
modal state = case state ^. _showModal of
  Nothing -> text ""
  Just view ->
    div [ classes overlayClass ]
      [ div [ classes [ ClassName "modal" ] ]
          [ modalContent view ]
      ]
  where
  overlayClass =
    if hasGlobalLoading state then
      [ ClassName "overlay" ]
    else
      [ ClassName "overlay", ClassName "overlay-background" ]

  modalContent = case _ of
    NewProject -> renderSubmodule _newProject NewProjectAction NewProject.render state
    OpenProject -> renderSubmodule _projects ProjectsAction Projects.render state
    OpenDemo -> renderSubmodule identity DemosAction Demos.render state
    RenameProject -> renderSubmodule _rename RenameAction Rename.render state
    SaveProjectAs -> renderSubmodule _saveAs SaveAsAction SaveAs.render state
    (ConfirmUnsavedNavigation intendedAction) -> ConfirmUnsavedNavigation.render intendedAction state
    (GithubLogin intendedAction) -> authButton intendedAction state
