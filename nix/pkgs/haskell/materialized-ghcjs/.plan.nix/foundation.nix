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
    flags = {
      experimental = false;
      bench-all = false;
      minimal-deps = false;
      bounds-check = false;
      doctest = false;
      linktest = false;
      };
    package = {
      specVersion = "1.18";
      identifier = { name = "foundation"; version = "0.0.26.1"; };
      license = "BSD-3-Clause";
      copyright = "2015-2017 Vincent Hanquez <vincent@snarc.org>, 2017- Foundation Maintainers";
      maintainer = "vincent@snarc.org";
      author = "Vincent Hanquez <vincent@snarc.org>";
      homepage = "https://github.com/haskell-foundation/foundation";
      url = "";
      synopsis = "Alternative prelude with batteries and no dependencies";
      description = "A custom prelude with no dependencies apart from base.\n\nThis package has the following goals:\n\n* provide a base like sets of modules that provide a consistent set of features and bugfixes across multiple versions of GHC (unlike base).\n\n* provide a better and more efficient prelude than base's prelude.\n\n* be self-sufficient: no external dependencies apart from base.\n\n* provide better data-types: packed unicode string by default, arrays.\n\n* Better numerical classes that better represent mathematical thing (No more all-in-one Num).\n\n* Better I/O system with less Lazy IO\n\n* Usual partial functions distinguished through type system";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [ "cbits/*.h" ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."basement" or (errorHandler.buildDepError "basement"))
          ] ++ (pkgs.lib).optionals (!(compiler.isGhc && (compiler.version).lt "8.0")) ([
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."ghc-prim" or (errorHandler.buildDepError "ghc-prim"))
          ] ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."Win32" or (errorHandler.buildDepError "Win32")));
        libs = (pkgs.lib).optionals (!(compiler.isGhc && (compiler.version).lt "8.0")) ((pkgs.lib).optionals (system.isWindows) ((pkgs.lib).optional (system.isI386) (pkgs."gcc" or (errorHandler.sysDepError "gcc"))));
        buildable = if compiler.isGhc && (compiler.version).lt "8.0"
          then false
          else true;
        modules = ((([
          "Foundation/Tuple"
          "Foundation/Hashing/FNV"
          "Foundation/Hashing/SipHash"
          "Foundation/Hashing/Hasher"
          "Foundation/Hashing/Hashable"
          "Foundation/Check/Gen"
          "Foundation/Check/Print"
          "Foundation/Check/Arbitrary"
          "Foundation/Check/Property"
          "Foundation/Check/Config"
          "Foundation/Check/Types"
          "Foundation/Collection/Buildable"
          "Foundation/Collection/List"
          "Foundation/Collection/Element"
          "Foundation/Collection/InnerFunctor"
          "Foundation/Collection/Collection"
          "Foundation/Collection/Copy"
          "Foundation/Collection/Sequential"
          "Foundation/Collection/Keyed"
          "Foundation/Collection/Indexed"
          "Foundation/Collection/Foldable"
          "Foundation/Collection/Mutable"
          "Foundation/Collection/Zippable"
          "Foundation/Collection/Mappable"
          "Foundation/Conduit/Internal"
          "Foundation/Format/CSV/Types"
          "Foundation/Format/CSV/Builder"
          "Foundation/Format/CSV/Parser"
          "Foundation/Numerical/Floating"
          "Foundation/IO/File"
          "Foundation/Monad/MonadIO"
          "Foundation/Monad/Exception"
          "Foundation/Monad/Transformer"
          "Foundation/Monad/Identity"
          "Foundation/Monad/Base"
          "Foundation/Random/Class"
          "Foundation/Random/DRG"
          "Foundation/Random/ChaChaDRG"
          "Foundation/Random/XorShift"
          "Foundation/Array/Chunked/Unboxed"
          "Foundation/Array/Bitmap"
          "Foundation/Foreign/Alloc"
          "Foundation/Foreign/MemoryMap"
          "Foundation/Foreign/MemoryMap/Types"
          "Foundation/Partial"
          "Foundation/System/Entropy/Common"
          "Foundation/System/Bindings/Network"
          "Foundation/System/Bindings/Time"
          "Foundation/System/Bindings/Hs"
          "Foundation"
          "Foundation/Numerical"
          "Foundation/Array"
          "Foundation/Array/Internal"
          "Foundation/Bits"
          "Foundation/Class/Bifunctor"
          "Foundation/Class/Storable"
          "Foundation/Conduit"
          "Foundation/Conduit/Textual"
          "Foundation/Exception"
          "Foundation/Format/CSV"
          "Foundation/String"
          "Foundation/String/Read"
          "Foundation/String/Builder"
          "Foundation/IO"
          "Foundation/IO/FileMap"
          "Foundation/IO/Terminal"
          "Foundation/VFS"
          "Foundation/VFS/Path"
          "Foundation/VFS/FilePath"
          "Foundation/VFS/URI"
          "Foundation/Math/Trigonometry"
          "Foundation/Hashing"
          "Foundation/Foreign"
          "Foundation/Collection"
          "Foundation/Primitive"
          "Foundation/List/DList"
          "Foundation/List/ListN"
          "Foundation/Monad"
          "Foundation/Monad/Except"
          "Foundation/Monad/Reader"
          "Foundation/Monad/State"
          "Foundation/Network/IPv4"
          "Foundation/Network/IPv6"
          "Foundation/System/Info"
          "Foundation/Strict"
          "Foundation/Parser"
          "Foundation/Random"
          "Foundation/Check"
          "Foundation/Check/Main"
          "Foundation/Timing"
          "Foundation/Timing/Main"
          "Foundation/Time/Types"
          "Foundation/Time/Bindings"
          "Foundation/Time/StopWatch"
          "Foundation/Tuple/Nth"
          "Foundation/UUID"
          "Foundation/System/Entropy"
          "Foundation/System/Bindings"
          ] ++ (pkgs.lib).optional (flags.experimental) "Foundation/Network/HostName") ++ (if system.isWindows
          then [
            "Foundation/Foreign/MemoryMap/Windows"
            "Foundation/System/Entropy/Windows"
            "Foundation/System/Bindings/Windows"
            ]
          else [
            "Foundation/Foreign/MemoryMap/Posix"
            "Foundation/System/Entropy/Unix"
            "Foundation/System/Bindings/Posix"
            "Foundation/System/Bindings/PosixDef"
            ])) ++ (pkgs.lib).optional (system.isLinux) "Foundation/System/Bindings/Linux") ++ (pkgs.lib).optional (system.isOsx) "Foundation/System/Bindings/Macos";
        cSources = [
          "cbits/foundation_random.c"
          "cbits/foundation_network.c"
          "cbits/foundation_time.c"
          "cbits/foundation_utf8.c"
          ];
        jsSources = (pkgs.lib).optional (system.isGhcjs) "jsbits/foundation.js";
        includeDirs = [ "cbits" ];
        };
      tests = {
        "check-foundation" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."basement" or (errorHandler.buildDepError "basement"))
            (hsPkgs."foundation" or (errorHandler.buildDepError "foundation"))
            ];
          buildable = true;
          modules = [
            "Test/Checks/Property/Collection"
            "Test/Foundation/Random"
            "Test/Foundation/Misc"
            "Test/Foundation/Conduit"
            "Test/Foundation/Primitive/BlockN"
            "Test/Foundation/Storable"
            "Test/Foundation/Number"
            "Test/Foundation/String/Base64"
            "Test/Foundation/String"
            "Test/Foundation/Bits"
            "Test/Basement"
            "Test/Basement/UTF8"
            "Test/Data/Network"
            "Test/Data/List"
            "Test/Foundation/Network/IPv4"
            "Test/Foundation/Network/IPv6"
            "Test/Foundation/Format"
            "Test/Foundation/Format/CSV"
            ];
          hsSourceDirs = [ "tests" ];
          mainPath = [ "Checks.hs" ];
          };
        "foundation-link" = {
          depends = (pkgs.lib).optionals (flags.linktest) [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."foundation" or (errorHandler.buildDepError "foundation"))
            (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
            ];
          buildable = if flags.linktest then true else false;
          hsSourceDirs = [ "tests" ];
          mainPath = [ "Scripts/Link.hs" ];
          };
        "doctest" = {
          depends = (pkgs.lib).optionals (!flags.minimal-deps) ((pkgs.lib).optionals (flags.doctest) [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."doctest" or (errorHandler.buildDepError "doctest"))
            ]);
          buildable = if flags.minimal-deps
            then false
            else if flags.doctest then true else false;
          hsSourceDirs = [ "tests" ];
          mainPath = [ "DocTest.hs" ];
          };
        };
      benchmarks = {
        "bench" = {
          depends = (pkgs.lib).optionals (!(flags.minimal-deps || compiler.isGhc && (compiler.version).lt "7.10")) ([
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."gauge" or (errorHandler.buildDepError "gauge"))
            (hsPkgs."basement" or (errorHandler.buildDepError "basement"))
            (hsPkgs."foundation" or (errorHandler.buildDepError "foundation"))
            ] ++ (pkgs.lib).optionals (flags.bench-all) [
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."attoparsec" or (errorHandler.buildDepError "attoparsec"))
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            ]);
          buildable = if flags.minimal-deps || compiler.isGhc && (compiler.version).lt "7.10"
            then false
            else true;
          modules = [
            "BenchUtil/Common"
            "BenchUtil/RefData"
            "Sys"
            "LargeWords"
            "Fake/ByteString"
            "Fake/Text"
            "Fake/Vector"
            ];
          hsSourceDirs = [ "benchs" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../contrib/foundation-0.0.26.1; }