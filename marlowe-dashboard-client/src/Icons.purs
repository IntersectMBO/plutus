-- TODO: replace web-common Icons module with this one
module Material.Icons
  ( add
  , addCircle
  , close
  , contacts
  , help
  , image
  , libraryAdd
  , menu
  , navigateBefore
  , navigateNext
  , notifications
  , personAdd
  , search
  , wallet
  ) where

import Prelude
import Halogen.HTML (ClassName(ClassName), HTML, span, text)
import Halogen.HTML.Properties (class_)

icon :: forall p i. String -> HTML p i
icon str = span [ class_ $ ClassName "material-icons" ] [ text str ]

-----
add :: forall p i. HTML p i
add = icon "add"

addCircle :: forall p i. HTML p i
addCircle = icon "add_circle"

close :: forall p i. HTML p i
close = icon "close"

contacts :: forall p i. HTML p i
contacts = icon "contacts"

help :: forall p i. HTML p i
help = icon "help"

image :: forall p i. HTML p i
image = icon "image"

libraryAdd :: forall p i. HTML p i
libraryAdd = icon "library_add"

menu :: forall p i. HTML p i
menu = icon "menu"

navigateBefore :: forall p i. HTML p i
navigateBefore = icon "navigate_before"

navigateNext :: forall p i. HTML p i
navigateNext = icon "navigate_next"

notifications :: forall p i. HTML p i
notifications = icon "notifications_none"

personAdd :: forall p i. HTML p i
personAdd = icon "person_add"

search :: forall p i. HTML p i
search = icon "search"

wallet :: forall p i. HTML p i
wallet = icon "account_balance_wallet"
