{ mkDerivation, aeson, aeson-better-errors, aeson-pretty
  , ansi-terminal, ansi-wl-pprint, array, base, base-compat
  , blaze-html, bower-json, boxes, bytestring, Cabal, cheapskate
  , clock, containers, data-ordlist, deepseq, directory, dlist
  , edit-distance, file-embed, filepath, fsnotify, gitrev, Glob
  , happy, haskeline, http-types, language-javascript, lifted-async
  , lifted-base, microlens-platform, monad-control, monad-logger, mtl
  , network, optparse-applicative, parallel, parsec, pattern-arrows
  , process, protolude, regex-tdfa, safe, scientific, semigroups
  , sourcemap, split, stdenv, stm, stringsearch, syb, text, time
  , transformers, transformers-base, transformers-compat
  , unordered-containers, utf8-string, vector, wai, wai-websockets
  , warp, websockets
  }:
  mkDerivation {
    pname = "purescript";
    version = "0.13.2";
    sha256 = "14ef4d299b3585e029373851fa0b3d42bea66df7e179da2ceebde46175178f3c";
    isLibrary = true;
    isExecutable = true;
    jailbreak = true;
    libraryHaskellDepends = [
      aeson aeson-better-errors aeson-pretty ansi-terminal array base
      base-compat blaze-html bower-json boxes bytestring Cabal cheapskate
      clock containers data-ordlist deepseq directory dlist edit-distance
      file-embed filepath fsnotify Glob haskeline language-javascript
      lifted-async lifted-base microlens-platform monad-control
      monad-logger mtl parallel parsec pattern-arrows process protolude
      regex-tdfa safe scientific semigroups sourcemap split stm
      stringsearch syb text time transformers transformers-base
      transformers-compat unordered-containers utf8-string vector
    ];
    libraryToolDepends = [ happy ];
    executableHaskellDepends = [
      aeson aeson-better-errors aeson-pretty ansi-terminal ansi-wl-pprint
      array base base-compat blaze-html bower-json boxes bytestring Cabal
      cheapskate clock containers data-ordlist deepseq directory dlist
      edit-distance file-embed filepath fsnotify gitrev Glob haskeline
      http-types language-javascript lifted-async lifted-base
      microlens-platform monad-control monad-logger mtl network
      optparse-applicative parallel parsec pattern-arrows process
      protolude regex-tdfa safe scientific semigroups sourcemap split stm
      stringsearch syb text time transformers transformers-base
      transformers-compat unordered-containers utf8-string vector wai
      wai-websockets warp websockets
    ];
    executableToolDepends = [ happy ];
    doHaddock = false;
    doCheck = false;
    homepage = "http://www.purescript.org/";
    description = "PureScript Programming Language Compiler";
    license = stdenv.lib.licenses.bsd3;
  }