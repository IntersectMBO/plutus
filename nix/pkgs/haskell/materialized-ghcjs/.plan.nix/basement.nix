{ system
  , compiler
  , flags
  , pkgs
  , hsPkgs
  , pkgconfPkgs
  , errorHandler
  , config
  , ... }:
  {
    flags = {};
    package = {
      specVersion = "1.18";
      identifier = { name = "basement"; version = "0.0.12"; };
      license = "BSD-3-Clause";
      copyright = "2015-2017 Vincent Hanquez <vincent@snarc.org>\n, 2017-2018 Foundation Maintainers";
      maintainer = "vincent@snarc.org";
      author = "";
      homepage = "https://github.com/haskell-foundation/foundation#readme";
      url = "";
      synopsis = "Foundation scrap box of array & string";
      description = "Foundation most basic primitives without any dependencies";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [ "cbits/*.h" "cbits/basement_rts.c" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = (pkgs.lib).optionals (!(compiler.isGhc && (compiler.version).lt "8.0")) ([
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."ghc-prim" or (errorHandler.buildDepError "ghc-prim"))
          ] ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."Win32" or (errorHandler.buildDepError "Win32")));
        buildable = if compiler.isGhc && (compiler.version).lt "8.0"
          then false
          else true;
        modules = [
          "Basement/Error"
          "Basement/Show"
          "Basement/Runtime"
          "Basement/Alg/Class"
          "Basement/Alg/Mutable"
          "Basement/Alg/PrimArray"
          "Basement/Alg/UTF8"
          "Basement/Alg/String"
          "Basement/Numerical/Conversion"
          "Basement/Block/Base"
          "Basement/UTF8/Base"
          "Basement/UTF8/Helper"
          "Basement/UTF8/Table"
          "Basement/UTF8/Types"
          "Basement/UArray/Base"
          "Basement/String/CaseMapping"
          "Basement/String/Encoding/Encoding"
          "Basement/String/Encoding/UTF16"
          "Basement/String/Encoding/UTF32"
          "Basement/String/Encoding/ASCII7"
          "Basement/String/Encoding/ISO_8859_1"
          "Basement/Terminal/Size"
          "Basement/Imports"
          "Basement/Base16"
          "Basement/Bindings/Memory"
          "Basement/Endianness"
          "Basement/Environment"
          "Basement/PrimType"
          "Basement/Exception"
          "Basement/Cast"
          "Basement/From"
          "Basement/Types/Char7"
          "Basement/Types/CharUTF8"
          "Basement/Types/OffsetSize"
          "Basement/Types/Ptr"
          "Basement/Types/AsciiString"
          "Basement/Types/Word128"
          "Basement/Types/Word256"
          "Basement/Monad"
          "Basement/MutableBuilder"
          "Basement/FinalPtr"
          "Basement/Nat"
          "Basement/BoxedArray"
          "Basement/Block"
          "Basement/Block/Mutable"
          "Basement/Block/Builder"
          "Basement/UArray"
          "Basement/UArray/Mutable"
          "Basement/String"
          "Basement/String/Builder"
          "Basement/NonEmpty"
          "Basement/Sized/Block"
          "Basement/Sized/UVect"
          "Basement/Sized/Vect"
          "Basement/Sized/List"
          "Basement/BlockN"
          "Basement/NormalForm"
          "Basement/These"
          "Basement/Terminal"
          "Basement/Terminal/ANSI"
          "Basement/IntegralConv"
          "Basement/Floating"
          "Basement/Numerical/Number"
          "Basement/Numerical/Additive"
          "Basement/Numerical/Subtractive"
          "Basement/Numerical/Multiplicative"
          "Basement/Bounded"
          "Basement/Alg/XorShift"
          "Basement/Compat/AMP"
          "Basement/Compat/Base"
          "Basement/Compat/Bifunctor"
          "Basement/Compat/CallStack"
          "Basement/Compat/C/Types"
          "Basement/Compat/ExtList"
          "Basement/Compat/IsList"
          "Basement/Compat/Identity"
          "Basement/Compat/Primitive"
          "Basement/Compat/PrimTypes"
          "Basement/Compat/MonadTrans"
          "Basement/Compat/Semigroup"
          "Basement/Compat/Natural"
          "Basement/Compat/NumLiteral"
          "Basement/Compat/Typeable"
          "Basement/Bits"
          ];
        cSources = [
          "cbits/foundation_mem.c"
          ] ++ (pkgs.lib).optional (compiler.isGhc && (compiler.version).lt "8.2") "cbits/basement_rts.c";
        jsSources = (pkgs.lib).optional (system.isGhcjs) "jsbits/basement.js";
        hsSourceDirs = [ "." ];
        includeDirs = [ "cbits" ];
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../contrib/basement-0.0.12; }