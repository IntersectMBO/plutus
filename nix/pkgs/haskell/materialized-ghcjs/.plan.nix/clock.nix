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
    flags = { llvm = false; };
    package = {
      specVersion = "1.10";
      identifier = { name = "clock"; version = "0.8.2"; };
      license = "BSD-3-Clause";
      copyright = "Copyright © Cetin Sert 2009-2016, Eugene Kirpichov 2010, Finn Espen Gundersen 2013, Gerolf Seitz 2013, Mathieu Boespflug 2014 2015, Chris Done 2015, Dimitri Sabadie 2015, Christian Burger 2015, Mario Longobardi 2016, Alexander Vershilov 2021.";
      maintainer = "Cetin Sert <cetin@sert.works>, Corsis Research";
      author = "Cetin Sert <cetin@sert.works>, Corsis Research";
      homepage = "https://github.com/corsis/clock";
      url = "";
      synopsis = "High-resolution clock functions: monotonic, realtime, cputime.";
      description = "A package for convenient access to high-resolution clock and\ntimer functions of different operating systems via a unified API.\n\nPOSIX code and surface API was developed by Cetin Sert in 2009.\n\nWindows code was contributed by Eugene Kirpichov in 2010.\n\nFreeBSD code was contributed by Finn Espen Gundersen on 2013-10-14.\n\nOS X code was contributed by Gerolf Seitz on 2013-10-15.\n\nDerived @Generic@, @Typeable@ and other instances for @Clock@ and @TimeSpec@ was contributed by Mathieu Boespflug on 2014-09-17.\n\nCorrected dependency listing for @GHC < 7.6@ was contributed by Brian McKenna on 2014-09-30.\n\nWindows code corrected by Dimitri Sabadie on 2015-02-09.\n\nAdded @timeSpecAsNanoSecs@ as observed widely-used by Chris Done on 2015-01-06, exported correctly on 2015-04-20.\n\nImported Control.Applicative operators correctly for Haskell Platform on Windows on 2015-04-21.\n\nUnit tests and instance fixes by Christian Burger on 2015-06-25.\n\nRemoval of fromInteger : Integer -> TimeSpec by Cetin Sert on 2015-12-15.\n\nNew Linux-specific Clocks: MonotonicRaw, Boottime, MonotonicCoarse, RealtimeCoarse by Cetin Sert on 2015-12-15.\n\nReintroduction fromInteger : Integer -> TimeSpec by Cetin Sert on 2016-04-05.\n\nFixes for older Linux build failures introduced by new Linux-specific clocks by Mario Longobardi on 2016-04-18.\n\nRefreshment release in 2019-04 after numerous contributions.\n\nRefactoring for Windows, Mac implementation consistence by Alexander Vershilov on 2021-01-16.\n\n[Version Scheme]\nMajor-@/R/@-ewrite . New-@/F/@-unctionality . @/I/@-mprovementAndBugFixes . @/P/@-ackagingOnly\n\n* @PackagingOnly@ changes are made for quality assurance reasons.";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          ] ++ (pkgs.lib).optionals (compiler.isGhc && (compiler.version).lt "7.6") [
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."ghc-prim" or (errorHandler.buildDepError "ghc-prim"))
          ];
        buildable = true;
        modules = [ "System/Clock" ];
        cSources = (pkgs.lib).optional (system.isWindows) "cbits/hs_clock_win32.c";
        jsSources = (pkgs.lib).optional (system.isGhcjs) "jsbits/gettime.js";
        includeDirs = [ "cbits" ];
        };
      tests = {
        "test" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."tasty" or (errorHandler.buildDepError "tasty"))
            (hsPkgs."tasty-quickcheck" or (errorHandler.buildDepError "tasty-quickcheck"))
            (hsPkgs."clock" or (errorHandler.buildDepError "clock"))
            ];
          buildable = true;
          hsSourceDirs = [ "tests" ];
          mainPath = [ "test.hs" ];
          };
        };
      benchmarks = {
        "benchmarks" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."criterion" or (errorHandler.buildDepError "criterion"))
            (hsPkgs."clock" or (errorHandler.buildDepError "clock"))
            ];
          buildable = true;
          hsSourceDirs = [ "bench" ];
          };
        };
      };
    } // rec { src = (pkgs.lib).mkDefault ../contrib/clock-0.8.2; }