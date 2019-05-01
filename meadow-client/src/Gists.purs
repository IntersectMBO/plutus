module Gists
  ( gistControls
  , mkNewGist
  ) where

import AjaxUtils
  ( showAjaxError
  )
import Auth
  ( AuthRole(..)
  , AuthStatus
  , authStatusAuthRole
  )
import Bootstrap
  ( btn
  , btnDanger
  , btnInfo
  , btnPrimary
  , nbsp
  )
import Data.Array
  ( catMaybes
  )
import Data.Lens
  ( view
  )
import Data.Maybe
  ( Maybe(..)
  )
import Gist
  ( Gist
  , NewGist
      ( NewGist
      )
  , NewGistFile
      ( NewGistFile
      )
  , gistHtmlUrl
  )
import Halogen.HTML
  ( ClassName
      ( ClassName
      )
  , HTML
  , a
  , br_
  , div
  , div_
  , text
  )
import Halogen.HTML.Events
  ( input_
  , onClick
  )
import Halogen.HTML.Properties
  ( class_
  , classes
  , href
  , target
  )
import Icons
  ( Icon(..)
  , icon
  )
import Network.RemoteData
  ( RemoteData
      ( NotAsked
      , Loading
      , Failure
      , Success
      )
  )
import Prelude
  ( Unit
  , ($)
  , (<$>)
  )
import Servant.PureScript.Ajax
  ( AjaxError
  )
import Types
  ( Query(..)
  )

import Data.Array as Array

gistControls ::
  forall p.
  RemoteData AjaxError AuthStatus ->
  RemoteData AjaxError Gist ->
  HTML p (Query Unit)
gistControls authStatus createGistResult = div_ [ a publishAttributes publishContent
                                                , br_
                                                , div_ [ case createGistResult of
                                                         Success gist -> gistPane gist
                                                         Failure err -> showAjaxError err
                                                         Loading -> nbsp
                                                         NotAsked -> nbsp
                                                       ]
                                                ]
  where
  publishAttributes = case (view authStatusAuthRole <$> authStatus), createGistResult of
    Failure _, _ -> [ classes [ btn
                              , btnDanger
                              ]
                    ]
    _, Failure _ -> [ classes [ btn
                              , btnDanger
                              ]
                    ]
    Success Anonymous, _ -> [ classes [ btn
                                      , btnInfo
                                      ]
                            , href "/api/oauth/github"
                            ]
    Success GithubUser, NotAsked -> [ classes [ btn
                                              , btnPrimary
                                              ]
                                    , onClick $ input_ PublishGist
                                    ]
    Success GithubUser, Success _ -> [ classes [ btn
                                               , btnPrimary
                                               ]
                                     , onClick $ input_ PublishGist
                                     ]
    Loading, _ -> [ classes [ btn
                            , btnInfo
                            ]
                  ]
    _, Loading -> [ classes [ btn
                            , btnInfo
                            ]
                  ]
    NotAsked, _ -> [ classes [ btn
                             , btnInfo
                             ]
                   ]
  publishContent = case (view authStatusAuthRole <$> authStatus), createGistResult of
    Failure _, _ -> [ text "Failure"
                    ]
    _, Failure _ -> [ text "Failure"
                    ]
    Success Anonymous, _ -> [ icon Github
                            , nbsp
                            , text "Publish"
                            ]
    Success GithubUser, NotAsked -> [ icon Github
                                    , nbsp
                                    , text "Publish"
                                    ]
    Success GithubUser, Success _ -> [ icon Github
                                     , nbsp
                                     , text "Republish"
                                     ]
    Loading, _ -> [ icon Spinner
                  ]
    _, Loading -> [ icon Spinner
                  ]
    NotAsked, _ -> [ icon Github
                   , nbsp
                   , text "Publish"
                   ]

gistPane ::
  forall p i.
  Gist ->
  HTML p i
gistPane gist = div [ class_ $ ClassName "gist-link"
                    ] [ a [ href $ view gistHtmlUrl gist
                          , target "_blank"
                          ] [ text $ "View on Github"
                            ]
                      ]

mkNewGist ::
  Maybe String ->
  Maybe NewGist
mkNewGist mSource = if Array.null gistFiles
  then Nothing
  else Just $ NewGist { _newGistDescription: "Plutus Playground Smart Contract"
                      , _newGistPublic: true
                      , _newGistFiles: gistFiles
                      }
  where
  gistFiles = catMaybes [ mkNewGistFile "Playground.hs" <$> mSource
                        ]
  mkNewGistFile _newGistFilename _newGistFileContent = NewGistFile { _newGistFilename
                                                                   , _newGistFileContent
                                                                   }
