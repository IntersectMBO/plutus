module Logo (plutusLogo) where

foreign import plutusLogoData :: String

-- The foreign import for this could more simply go in MainFrame/View.purs
-- (where the logo is used). However, if it goes in a subdirectory, webpack
-- inexplicably wants different paths in development and production. Until
-- that mystery is solved (or a better way of handling the logo presents
-- itself), this will have to do.
plutusLogo :: String
plutusLogo = plutusLogoData
