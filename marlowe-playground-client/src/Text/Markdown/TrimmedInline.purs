module Text.Markdown.TrimmedInline
  ( markdownToHTML
  ) where

import Prelude
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.State (StateT, evalStateT, get, modify)
import Data.Array as A
import Data.Either (Either(..))
import Data.Identity (Identity)
import Data.List (List(..))
import Data.List as L
import Data.Maybe as M
import Data.Newtype (unwrap)
import Data.Traversable (traverse)
import Halogen.HTML (HTML)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Text.Markdown.SlamDown as SD
import Text.Markdown.SlamDown.Parser (parseMd)
import Text.Markdown.SlamDown.Pretty (prettyPrintMd)

-- This code is a trimmed down version of the renderer in https://github.com/slamdata/purescript-markdown-halogen/
type FreshT m
  = ReaderT String (StateT Int m)

type Fresh
  = FreshT Identity

fresh ::
  forall m.
  Monad m =>
  FreshT m String
fresh = do
  prefix <- ask
  n <- get :: FreshT m Int
  void $ modify (_ + 1)
  pure (prefix <> "-" <> show n)

runFreshT ::
  forall m.
  Monad m =>
  String ->
  FreshT m
    ~> m
runFreshT prefix m =
  evalStateT
    (runReaderT m prefix)
    1

runFresh ::
  forall a.
  String ->
  Fresh a ->
  a
runFresh prefix =
  unwrap
    <<< runFreshT prefix

type FreshRenderer v m a
  = a -> Fresh (HTML v m)

renderInline :: forall v m. SD.Inline String -> Fresh (HTML v m)
renderInline i = case i of
  SD.Str s -> pure $ HH.text s
  SD.Entity s -> pure $ HH.text s
  SD.Space -> pure $ HH.text " "
  SD.SoftBreak -> pure $ HH.text "\n"
  SD.LineBreak -> pure $ HH.br_
  SD.Emph is -> HH.em_ <$> traverse renderInline (A.fromFoldable is)
  SD.Strong is -> HH.strong_ <$> traverse renderInline (A.fromFoldable is)
  SD.Code _ c -> pure $ HH.code_ [ HH.text c ]
  SD.Link body tgt -> do
    let
      href (SD.InlineLink url) = url

      href (SD.ReferenceLink tgt') = M.maybe "" ("#" <> _) tgt'
    HH.a [ HP.href $ href tgt ] <$> traverse renderInline (A.fromFoldable body)
  other -> pure $ HH.text (prettyPrintMd (SD.SlamDown $ L.singleton $ SD.Paragraph $ L.singleton other :: SD.SlamDown))

renderSlamDownInline :: forall a p. SD.Inline String -> HTML p a
renderSlamDownInline i = runFresh "markdown" (renderInline i)

markdownToHTML :: forall a p. String -> Array (HTML p a)
markdownToHTML md = case parseMd md of
  Right (SD.SlamDown (Cons (SD.Paragraph singleLine) Nil)) -> map renderSlamDownInline (A.fromFoldable singleLine)
  _ -> [ HH.text md ]
