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
      compiler-only = false;
      no-wrapper-install = false;
      disable-optimizer = false;
      runtime-assertions = false;
      debug = false;
      ghci = true;
      stage1 = false;
      stage2 = true;
      stage3 = false;
      terminfo = true;
      };
    package = {
      specVersion = "2.4";
      identifier = { name = "ghcjs"; version = "8.10.7"; };
      license = "MIT";
      copyright = "Victor Nazarov, Hamish Mackenzie, Luite Stegeman";
      maintainer = "Luite Stegeman <stegeman@gmail.com>";
      author = "Victor Nazarov, Hamish Mackenzie, Luite Stegeman";
      homepage = "";
      url = "";
      synopsis = "Haskell to JavaScript compiler";
      description = "Haskell to JavaScript compiler based on GHC";
      buildType = "Simple";
      isLocal = true;
      detailLevel = "FullDetails";
      licenseFiles = [ "LICENSE" ];
      dataDir = ".";
      dataFiles = [];
      extraSrcFiles = [
        "utils/*.hs"
        "utils/*.sh"
        "include/prim/*.hs-incl"
        "include/prim/*.txt"
        "include/*.h"
        "src-bin/haddock/*.hs"
        "HACKING.markdown"
        "README.markdown"
        "test/LICENSE"
        "test/ghcjs-testsuite.cabal"
        "stack.yaml"
        "cabal.project"
        "inplace/bin/README.markdown"
        "ghc/compiler/Unique.h"
        "ghc/compiler/HsVersions.h"
        "ghc/compiler/parser/cutils.h"
        "ghc/includes/CodeGen.Platform.hs"
        "lib/ghc/includes/*.h"
        "lib/ghc/includes/*.hs"
        "lib/ghc/includes/*.hs-incl"
        "ghc/includes/rts/*.h"
        "ghc/includes/rts/storage/*.h"
        "ghc/includes/MachDeps.h"
        "ghc/includes/Rts.h"
        "ghc/includes/RtsAPI.h"
        "ghc/includes/Stg.h"
        "ghc/includes/HsFFI.h"
        "ghc/includes/Cmm.h"
        "ghc/includes/stg/*.h"
        "ghc/utils/unlit/fs.h"
        "ghc/driver/utils/cwrapper.h"
        "ghc/driver/utils/getLocation.h"
        "utils/wrapper/getline.h"
        ];
      extraTmpFiles = [];
      extraDocFiles = [];
      };
    components = {
      "library" = {
        depends = [
          (hsPkgs."ghci" or (errorHandler.buildDepError "ghci"))
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."Cabal" or (errorHandler.buildDepError "Cabal"))
          (hsPkgs."ghc-boot" or (errorHandler.buildDepError "ghc-boot"))
          (hsPkgs."ghc-heap" or (errorHandler.buildDepError "ghc-heap"))
          (hsPkgs."ghc-compact" or (errorHandler.buildDepError "ghc-compact"))
          (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
          (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."process" or (errorHandler.buildDepError "process"))
          (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
          (hsPkgs."ghc-paths" or (errorHandler.buildDepError "ghc-paths"))
          (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
          (hsPkgs."syb" or (errorHandler.buildDepError "syb"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."attoparsec" or (errorHandler.buildDepError "attoparsec"))
          (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
          (hsPkgs."text" or (errorHandler.buildDepError "text"))
          (hsPkgs."wl-pprint-text" or (errorHandler.buildDepError "wl-pprint-text"))
          (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
          (hsPkgs."yaml" or (errorHandler.buildDepError "yaml"))
          (hsPkgs."time" or (errorHandler.buildDepError "time"))
          (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
          (hsPkgs."split" or (errorHandler.buildDepError "split"))
          (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
          (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
          (hsPkgs."data-default" or (errorHandler.buildDepError "data-default"))
          (hsPkgs."array" or (errorHandler.buildDepError "array"))
          (hsPkgs."binary" or (errorHandler.buildDepError "binary"))
          (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
          (hsPkgs."parallel" or (errorHandler.buildDepError "parallel"))
          (hsPkgs."cryptohash" or (errorHandler.buildDepError "cryptohash"))
          (hsPkgs."hashable" or (errorHandler.buildDepError "hashable"))
          (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
          (hsPkgs."stringsearch" or (errorHandler.buildDepError "stringsearch"))
          (hsPkgs."base16-bytestring" or (errorHandler.buildDepError "base16-bytestring"))
          (hsPkgs."base64-bytestring" or (errorHandler.buildDepError "base64-bytestring"))
          (hsPkgs."safe" or (errorHandler.buildDepError "safe"))
          (hsPkgs."parsec" or (errorHandler.buildDepError "parsec"))
          (hsPkgs."base" or (errorHandler.buildDepError "base"))
          (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
          (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
          (hsPkgs."process" or (errorHandler.buildDepError "process"))
          (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
          (hsPkgs."binary" or (errorHandler.buildDepError "binary"))
          (hsPkgs."time" or (errorHandler.buildDepError "time"))
          (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
          (hsPkgs."array" or (errorHandler.buildDepError "array"))
          (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
          (hsPkgs."template-haskell" or (errorHandler.buildDepError "template-haskell"))
          (hsPkgs."hpc" or (errorHandler.buildDepError "hpc"))
          (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
          (hsPkgs."ghc-boot" or (errorHandler.buildDepError "ghc-boot"))
          (hsPkgs."ghc-boot-th" or (errorHandler.buildDepError "ghc-boot-th"))
          (hsPkgs."ghc-heap" or (errorHandler.buildDepError "ghc-heap"))
          (hsPkgs."ghci" or (errorHandler.buildDepError "ghci"))
          ] ++ (if system.isWindows
          then [ (hsPkgs."Win32" or (errorHandler.buildDepError "Win32")) ]
          else [
            (hsPkgs."unix" or (errorHandler.buildDepError "unix"))
            ] ++ (pkgs.lib).optional (flags.terminfo) (hsPkgs."terminfo" or (errorHandler.buildDepError "terminfo")));
        build-tools = [
          (hsPkgs.buildPackages.happy.components.exes.happy or (pkgs.buildPackages.happy or (errorHandler.buildToolDepError "happy:happy")))
          ];
        buildable = true;
        modules = [
          "Paths_ghcjs"
          "Gen2/Generator"
          "Gen2/Profiling"
          "Gen2/Floater"
          "Gen2/Prim"
          "Gen2/Rts"
          "Gen2/RtsApply"
          "Gen2/RtsTypes"
          "Gen2/RtsAlloc"
          "Gen2/Utils"
          "Gen2/StgAst"
          "Gen2/Optimizer"
          "Gen2/Dataflow"
          "Gen2/Deps"
          "Gen2/Printer"
          "Gen2/Linker"
          "Gen2/Shim"
          "Gen2/Compactor"
          "Gen2/Object"
          "Gen2/Archive"
          "Gen2/ClosureInfo"
          "Gen2/Foreign"
          "Gen2/Sinker"
          "Gen2/TH"
          "Gen2/Base"
          "Gen2/Cache"
          "Gen2/DynamicLinking"
          "Gen2/GHC/Digraph"
          "Gen2/GHC/DsForeign"
          "Compiler/Compat"
          "Compiler/GhcjsHooks"
          "Compiler/GhcjsPlatform"
          "Compiler/Info"
          "Compiler/Plugins"
          "Compiler/Program"
          "Compiler/GhcjsProgram"
          "Compiler/Platform"
          "Compiler/Settings"
          "Compiler/Utils"
          "Compiler/Variants"
          "Compiler/JMacro"
          "Compiler/JMacro/Base"
          "Compiler/JMacro/Lens"
          "Compiler/JMacro/QQ"
          "Compiler/JMacro/Util"
          "Compiler/JMacro/Combinators"
          "Compiler/JMacro/Symbols"
          "GHCJS"
          "GHCJS/Prim/TH/Eval"
          "GHCJS/Prim/TH/Types"
          "HieTypes"
          "HieDebug"
          "HieBin"
          "HieUtils"
          "HieAst"
          "Ar"
          "FileCleanup"
          "DriverBkp"
          "BkpSyn"
          "NameShape"
          "RnModIface"
          "Avail"
          "AsmUtils"
          "BasicTypes"
          "ConLike"
          "DataCon"
          "PatSyn"
          "Demand"
          "Debug"
          "Exception"
          "FieldLabel"
          "GhcMonad"
          "Hooks"
          "Id"
          "IdInfo"
          "Predicate"
          "Lexeme"
          "Literal"
          "Llvm"
          "Llvm/AbsSyn"
          "Llvm/MetaData"
          "Llvm/PpLlvm"
          "Llvm/Types"
          "LlvmCodeGen"
          "LlvmCodeGen/Base"
          "LlvmCodeGen/CodeGen"
          "LlvmCodeGen/Data"
          "LlvmCodeGen/Ppr"
          "LlvmCodeGen/Regs"
          "LlvmMangler"
          "MkId"
          "Module"
          "Name"
          "NameEnv"
          "NameSet"
          "OccName"
          "RdrName"
          "NameCache"
          "SrcLoc"
          "UniqSupply"
          "Unique"
          "Var"
          "VarEnv"
          "VarSet"
          "UnVarGraph"
          "BlockId"
          "CLabel"
          "Cmm"
          "CmmBuildInfoTables"
          "CmmPipeline"
          "CmmCallConv"
          "CmmCommonBlockElim"
          "CmmImplementSwitchPlans"
          "CmmContFlowOpt"
          "CmmExpr"
          "CmmInfo"
          "CmmLex"
          "CmmLint"
          "CmmLive"
          "CmmMachOp"
          "CmmMonad"
          "CmmSwitch"
          "CmmNode"
          "CmmOpt"
          "CmmParse"
          "CmmProcPoint"
          "CmmSink"
          "CmmType"
          "CmmUtils"
          "CmmLayoutStack"
          "CliOption"
          "EnumSet"
          "GhcNameVersion"
          "FileSettings"
          "MkGraph"
          "PprBase"
          "PprC"
          "PprCmm"
          "PprCmmDecl"
          "PprCmmExpr"
          "Bitmap"
          "GHC/Platform/Regs"
          "GHC/Platform/ARM"
          "GHC/Platform/AArch64"
          "GHC/Platform/NoRegs"
          "GHC/Platform/PPC"
          "GHC/Platform/S390X"
          "GHC/Platform/SPARC"
          "GHC/Platform/X86"
          "GHC/Platform/X86_64"
          "GHC/StgToCmm/CgUtils"
          "GHC/StgToCmm"
          "GHC/StgToCmm/Bind"
          "GHC/StgToCmm/Closure"
          "GHC/StgToCmm/DataCon"
          "GHC/StgToCmm/Env"
          "GHC/StgToCmm/Expr"
          "GHC/StgToCmm/Foreign"
          "GHC/StgToCmm/Heap"
          "GHC/StgToCmm/Hpc"
          "GHC/StgToCmm/ArgRep"
          "GHC/StgToCmm/Layout"
          "GHC/StgToCmm/Monad"
          "GHC/StgToCmm/Prim"
          "GHC/StgToCmm/Prof"
          "GHC/StgToCmm/Ticky"
          "GHC/StgToCmm/Utils"
          "GHC/StgToCmm/ExtCode"
          "SMRep"
          "CoreArity"
          "CoreFVs"
          "CoreLint"
          "CorePrep"
          "CoreSubst"
          "CoreOpt"
          "CoreSyn"
          "TrieMap"
          "CoreTidy"
          "CoreUnfold"
          "CoreUtils"
          "CoreMap"
          "CoreSeq"
          "CoreStats"
          "MkCore"
          "PprCore"
          "GHC/HsToCore/PmCheck/Oracle"
          "GHC/HsToCore/PmCheck/Ppr"
          "GHC/HsToCore/PmCheck/Types"
          "GHC/HsToCore/PmCheck"
          "Coverage"
          "Desugar"
          "DsArrows"
          "DsBinds"
          "DsCCall"
          "DsExpr"
          "DsForeign"
          "DsGRHSs"
          "DsListComp"
          "DsMonad"
          "DsUsage"
          "DsUtils"
          "ExtractDocs"
          "Match"
          "MatchCon"
          "MatchLit"
          "GHC/Hs"
          "GHC/Hs/Binds"
          "GHC/Hs/Decls"
          "GHC/Hs/Doc"
          "GHC/Hs/Expr"
          "GHC/Hs/ImpExp"
          "GHC/Hs/Lit"
          "GHC/Hs/PlaceHolder"
          "GHC/Hs/Extension"
          "GHC/Hs/Instances"
          "GHC/Hs/Pat"
          "GHC/Hs/Types"
          "GHC/Hs/Utils"
          "GHC/Hs/Dump"
          "BinIface"
          "BinFingerprint"
          "BuildTyCl"
          "IfaceEnv"
          "IfaceSyn"
          "IfaceType"
          "ToIface"
          "LoadIface"
          "MkIface"
          "TcIface"
          "FlagChecker"
          "Annotations"
          "CmdLineParser"
          "CodeOutput"
          "Config"
          "Constants"
          "DriverMkDepend"
          "DriverPhases"
          "PipelineMonad"
          "DriverPipeline"
          "DynFlags"
          "ErrUtils"
          "Finder"
          "GHC"
          "GhcMake"
          "GhcPlugins"
          "GhcPrelude"
          "DynamicLoading"
          "HeaderInfo"
          "HscMain"
          "HscStats"
          "HscTypes"
          "InteractiveEval"
          "InteractiveEvalTypes"
          "PackageConfig"
          "Packages"
          "PlatformConstants"
          "Plugins"
          "TcPluginM"
          "PprTyThing"
          "Settings"
          "StaticPtrTable"
          "SysTools"
          "SysTools/BaseDir"
          "SysTools/Terminal"
          "SysTools/ExtraObj"
          "SysTools/Info"
          "SysTools/Process"
          "SysTools/Tasks"
          "SysTools/Settings"
          "Elf"
          "TidyPgm"
          "Ctype"
          "HaddockUtils"
          "Lexer"
          "OptCoercion"
          "Parser"
          "RdrHsSyn"
          "ApiAnnotation"
          "ForeignCall"
          "KnownUniques"
          "PrelInfo"
          "PrelNames"
          "PrelRules"
          "PrimOp"
          "ToolSettings"
          "TysPrim"
          "TysWiredIn"
          "CostCentre"
          "CostCentreState"
          "ProfInit"
          "RnBinds"
          "RnEnv"
          "RnExpr"
          "RnHsDoc"
          "RnNames"
          "RnPat"
          "RnSource"
          "RnSplice"
          "RnTypes"
          "RnFixity"
          "RnUtils"
          "RnUnbound"
          "CoreMonad"
          "CSE"
          "FloatIn"
          "FloatOut"
          "LiberateCase"
          "OccurAnal"
          "SAT"
          "SetLevels"
          "SimplCore"
          "SimplEnv"
          "SimplMonad"
          "SimplUtils"
          "Simplify"
          "SimplStg"
          "StgStats"
          "StgCse"
          "StgLiftLams"
          "StgLiftLams/Analysis"
          "StgLiftLams/LiftM"
          "StgLiftLams/Transformation"
          "StgSubst"
          "UnariseStg"
          "RepType"
          "Rules"
          "SpecConstr"
          "Specialise"
          "CoreToStg"
          "StgLint"
          "StgSyn"
          "StgFVs"
          "CallArity"
          "DmdAnal"
          "Exitify"
          "WorkWrap"
          "WwLib"
          "FamInst"
          "ClsInst"
          "Inst"
          "TcAnnotations"
          "TcArrows"
          "TcBinds"
          "TcSigs"
          "TcClassDcl"
          "TcDefaults"
          "TcDeriv"
          "TcDerivInfer"
          "TcDerivUtils"
          "TcEnv"
          "TcExpr"
          "TcForeign"
          "TcGenDeriv"
          "TcGenFunctor"
          "TcGenGenerics"
          "TcHsSyn"
          "TcHsType"
          "TcInstDcls"
          "TcMType"
          "TcValidity"
          "TcMatches"
          "TcPat"
          "TcPatSyn"
          "TcRnDriver"
          "TcBackpack"
          "TcRnExports"
          "TcRnMonad"
          "TcRnTypes"
          "Constraint"
          "TcOrigin"
          "TcRules"
          "TcSimplify"
          "TcHoleErrors"
          "TcHoleFitTypes"
          "TcErrors"
          "TcTyClsDecls"
          "TcTyDecls"
          "TcTypeable"
          "TcType"
          "TcEvidence"
          "TcEvTerm"
          "TcUnify"
          "TcInteract"
          "TcCanonical"
          "TcFlatten"
          "TcSMonad"
          "TcTypeNats"
          "TcSplice"
          "Class"
          "Coercion"
          "DsMeta"
          "THNames"
          "FamInstEnv"
          "FunDeps"
          "InstEnv"
          "TyCon"
          "CoAxiom"
          "Type"
          "TyCoRep"
          "TyCoFVs"
          "TyCoSubst"
          "TyCoPpr"
          "TyCoTidy"
          "Unify"
          "Bag"
          "Binary"
          "BooleanFormula"
          "BufWrite"
          "Digraph"
          "Encoding"
          "FastFunctions"
          "FastMutInt"
          "FastString"
          "FastStringEnv"
          "Fingerprint"
          "FiniteMap"
          "FV"
          "GraphBase"
          "GraphColor"
          "GraphOps"
          "GraphPpr"
          "IOEnv"
          "Json"
          "ListSetOps"
          "Maybes"
          "MonadUtils"
          "OrdList"
          "Outputable"
          "Pair"
          "Panic"
          "PlainPanic"
          "PprColour"
          "Pretty"
          "State"
          "Stream"
          "StringBuffer"
          "UniqDFM"
          "UniqDSet"
          "UniqFM"
          "UniqMap"
          "UniqSet"
          "Util"
          "Hoopl/Block"
          "Hoopl/Collections"
          "Hoopl/Dataflow"
          "Hoopl/Graph"
          "Hoopl/Label"
          "AsmCodeGen"
          "TargetReg"
          "NCGMonad"
          "Instruction"
          "BlockLayout"
          "CFG"
          "Dominators"
          "Format"
          "Reg"
          "RegClass"
          "PIC"
          "CPrim"
          "X86/Regs"
          "X86/RegInfo"
          "X86/Instr"
          "X86/Cond"
          "X86/Ppr"
          "X86/CodeGen"
          "PPC/Regs"
          "PPC/RegInfo"
          "PPC/Instr"
          "PPC/Cond"
          "PPC/Ppr"
          "PPC/CodeGen"
          "SPARC/Base"
          "SPARC/Regs"
          "SPARC/Imm"
          "SPARC/AddrMode"
          "SPARC/Cond"
          "SPARC/Instr"
          "SPARC/Stack"
          "SPARC/ShortcutJump"
          "SPARC/Ppr"
          "SPARC/CodeGen"
          "SPARC/CodeGen/Amode"
          "SPARC/CodeGen/Base"
          "SPARC/CodeGen/CondCode"
          "SPARC/CodeGen/Gen32"
          "SPARC/CodeGen/Gen64"
          "SPARC/CodeGen/Sanity"
          "SPARC/CodeGen/Expand"
          "RegAlloc/Liveness"
          "RegAlloc/Graph/Main"
          "RegAlloc/Graph/Stats"
          "RegAlloc/Graph/ArchBase"
          "RegAlloc/Graph/ArchX86"
          "RegAlloc/Graph/Coalesce"
          "RegAlloc/Graph/Spill"
          "RegAlloc/Graph/SpillClean"
          "RegAlloc/Graph/SpillCost"
          "RegAlloc/Graph/TrivColorable"
          "RegAlloc/Linear/Main"
          "RegAlloc/Linear/JoinToTargets"
          "RegAlloc/Linear/State"
          "RegAlloc/Linear/Stats"
          "RegAlloc/Linear/FreeRegs"
          "RegAlloc/Linear/StackMap"
          "RegAlloc/Linear/Base"
          "RegAlloc/Linear/X86/FreeRegs"
          "RegAlloc/Linear/X86_64/FreeRegs"
          "RegAlloc/Linear/PPC/FreeRegs"
          "RegAlloc/Linear/SPARC/FreeRegs"
          "Dwarf"
          "Dwarf/Types"
          "Dwarf/Constants"
          "GHC/ThToHs"
          "ByteCodeTypes"
          "ByteCodeAsm"
          "ByteCodeGen"
          "ByteCodeInstr"
          "ByteCodeItbls"
          "ByteCodeLink"
          "Debugger"
          "LinkerTypes"
          "Linker"
          "RtClosureInspect"
          "GHCi"
          ];
        cSources = [
          "ghc/compiler/parser/cutils.c"
          "ghc/compiler/cbits/genSym.c"
          ];
        hsSourceDirs = [
          "lib/ghcjs-th"
          "src"
          "lib/ghc/autogen"
          "ghc/compiler"
          "ghc/compiler/backpack"
          "ghc/compiler/basicTypes"
          "ghc/compiler/cmm"
          "ghc/compiler/coreSyn"
          "ghc/compiler/deSugar"
          "ghc/compiler/ghci"
          "ghc/compiler/hieFile"
          "ghc/compiler/iface"
          "ghc/compiler/llvmGen"
          "ghc/compiler/main"
          "ghc/compiler/nativeGen"
          "ghc/compiler/parser"
          "ghc/compiler/prelude"
          "ghc/compiler/profiling"
          "ghc/compiler/rename"
          "ghc/compiler/simplCore"
          "ghc/compiler/simplStg"
          "ghc/compiler/specialise"
          "ghc/compiler/stgSyn"
          "ghc/compiler/stranal"
          "ghc/compiler/typecheck"
          "ghc/compiler/types"
          "ghc/compiler/utils"
          ] ++ (if system.isWindows
          then [ "src-platform/windows" ]
          else [ "src-platform/unix" ]);
        includeDirs = [
          "ghc/compiler"
          "ghc/compiler/parser"
          "ghc/compiler/utils"
          "lib/ghc/includes"
          ];
        };
      exes = {
        "ghcjs" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."ghcjs" or (errorHandler.buildDepError "ghcjs"))
            ];
          buildable = true;
          hsSourceDirs = [ "src-bin" ];
          mainPath = [ "Main.hs" ];
          };
        "ghcjs-pkg" = {
          depends = [
            (hsPkgs."ghcjs" or (errorHandler.buildDepError "ghcjs"))
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."Cabal" or (errorHandler.buildDepError "Cabal"))
            (hsPkgs."binary" or (errorHandler.buildDepError "binary"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."ghc-boot" or (errorHandler.buildDepError "ghc-boot"))
            ] ++ (pkgs.lib).optionals (!system.isWindows) [
            (hsPkgs."unix" or (errorHandler.buildDepError "unix"))
            (hsPkgs."terminfo" or (errorHandler.buildDepError "terminfo"))
            ];
          buildable = if flags.compiler-only then false else true;
          cSources = (pkgs.lib).optional (system.isWindows) "cbits/CRT_noglob.c";
          hsSourceDirs = [ "src-bin" ];
          mainPath = (([
            "Pkg.hs"
            ] ++ (pkgs.lib).optional (flags.compiler-only) "") ++ (pkgs.lib).optional (!system.isWindows) "") ++ (pkgs.lib).optional (system.isWindows) "";
          };
        "ghcjs-boot" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."ghcjs" or (errorHandler.buildDepError "ghcjs"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."Cabal" or (errorHandler.buildDepError "Cabal"))
            (hsPkgs."mtl" or (errorHandler.buildDepError "mtl"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
            (hsPkgs."vector" or (errorHandler.buildDepError "vector"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            (hsPkgs."tar" or (errorHandler.buildDepError "tar"))
            (hsPkgs."yaml" or (errorHandler.buildDepError "yaml"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."unix-compat" or (errorHandler.buildDepError "unix-compat"))
            (hsPkgs."executable-path" or (errorHandler.buildDepError "executable-path"))
            ];
          buildable = true;
          hsSourceDirs = [ "src-bin" ];
          mainPath = [ "Boot.hs" ] ++ (pkgs.lib).optional (system.isWindows) "";
          };
        "private-ghcjs-run" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            ];
          buildable = if flags.compiler-only then false else true;
          hsSourceDirs = [ "src-bin" ];
          mainPath = ([
            "Run.hs"
            ] ++ (pkgs.lib).optional (flags.compiler-only) "") ++ (pkgs.lib).optional (system.isWindows) "";
          };
        "private-ghcjs-wrapper" = {
          buildable = if flags.compiler-only || !system.isWindows
            then false
            else true;
          cSources = [
            "ghc/driver/utils/getLocation.c"
            "ghc/driver/utils/cwrapper.c"
            "utils/wrapper/getline.c"
            ];
          hsSourceDirs = [ "utils/wrapper" ];
          includeDirs = [ "ghc/driver/utils" ];
          includes = [
            "ghc/driver/utils/cwrapper.h"
            "ghc/driver/utils/getLocation.h"
            "utils/wrapper/getline.h"
            ];
          mainPath = [
            "wrapper.c"
            ] ++ (pkgs.lib).optional (flags.compiler-only || !system.isWindows) "";
          };
        "private-ghcjs-unlit" = {
          buildable = if flags.compiler-only then false else true;
          cSources = [ "ghc/utils/unlit/fs.c" ];
          hsSourceDirs = [ "ghc/utils/unlit" ];
          includes = [ "ghc/utils/unlit/fs.h" ];
          mainPath = [
            "unlit.c"
            ] ++ (pkgs.lib).optional (flags.compiler-only) "";
          };
        "private-ghcjs-touchy" = {
          buildable = if flags.compiler-only || !system.isWindows
            then false
            else true;
          hsSourceDirs = [ "ghc/utils/touchy" ];
          mainPath = [
            "touchy.c"
            ] ++ (pkgs.lib).optional (flags.compiler-only || !system.isWindows) "";
          };
        "private-ghcjs-hsc2hs" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            ] ++ (pkgs.lib).optional (system.isWindows) (hsPkgs."process" or (errorHandler.buildDepError "process"));
          buildable = if flags.compiler-only then false else true;
          modules = [
            "C"
            "Common"
            "CrossCodegen"
            "DirectCodegen"
            "Flags"
            "HSCParser"
            "ATTParser"
            "UtilsCodegen"
            "Compat/ResponseFile"
            "Compat/TempFile"
            "Paths_ghcjs"
            ];
          hsSourceDirs = [ "ghc/utils/hsc2hs" ];
          mainPath = ([
            "Main.hs"
            ] ++ (pkgs.lib).optional (flags.compiler-only) "") ++ (pkgs.lib).optional (system.isWindows) "";
          };
        "haddock" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            ] ++ (pkgs.lib).optionals true [
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."containers" or (errorHandler.buildDepError "containers"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            (hsPkgs."array" or (errorHandler.buildDepError "array"))
            (hsPkgs."xhtml" or (errorHandler.buildDepError "xhtml"))
            (hsPkgs."Cabal" or (errorHandler.buildDepError "Cabal"))
            (hsPkgs."ghc-boot" or (errorHandler.buildDepError "ghc-boot"))
            (hsPkgs."ghcjs" or (errorHandler.buildDepError "ghcjs"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."parsec" or (errorHandler.buildDepError "parsec"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            ];
          buildable = if flags.compiler-only then false else true;
          modules = (pkgs.lib).optionals true [
            "CompatPrelude"
            "Documentation/Haddock/Parser"
            "Documentation/Haddock/Parser/Monad"
            "Documentation/Haddock/Parser/Identifier"
            "Documentation/Haddock/Types"
            "Documentation/Haddock/Doc"
            "Documentation/Haddock/Parser/Util"
            "Documentation/Haddock/Markup"
            "Documentation/Haddock"
            "Haddock"
            "Haddock/Interface"
            "Haddock/Interface/Json"
            "Haddock/Interface/Rename"
            "Haddock/Interface/Create"
            "Haddock/Interface/AttachInstances"
            "Haddock/Interface/LexParseRn"
            "Haddock/Interface/ParseModuleHeader"
            "Haddock/Interface/Specialize"
            "Haddock/Parser"
            "Haddock/Utils"
            "Haddock/Utils/Json"
            "Haddock/Backends/Xhtml"
            "Haddock/Backends/Xhtml/Decl"
            "Haddock/Backends/Xhtml/DocMarkup"
            "Haddock/Backends/Xhtml/Layout"
            "Haddock/Backends/Xhtml/Meta"
            "Haddock/Backends/Xhtml/Names"
            "Haddock/Backends/Xhtml/Themes"
            "Haddock/Backends/Xhtml/Types"
            "Haddock/Backends/Xhtml/Utils"
            "Haddock/Backends/LaTeX"
            "Haddock/Backends/HaddockDB"
            "Haddock/Backends/Hoogle"
            "Haddock/Backends/Hyperlinker"
            "Haddock/Backends/Hyperlinker/Parser"
            "Haddock/Backends/Hyperlinker/Renderer"
            "Haddock/Backends/Hyperlinker/Types"
            "Haddock/Backends/Hyperlinker/Utils"
            "Haddock/ModuleTree"
            "Haddock/Types"
            "Haddock/Doc"
            "Haddock/Version"
            "Haddock/InterfaceFile"
            "Haddock/Options"
            "Haddock/GhcUtils"
            "Haddock/Syb"
            "Haddock/Convert"
            "Paths_ghcjs"
            ];
          hsSourceDirs = [ "src-bin" ] ++ (pkgs.lib).optionals true [
            "ghc/utils/haddock/haddock-api/src"
            "ghc/utils/haddock/haddock-library/src"
            ];
          mainPath = ([
            "HaddockDriver.hs"
            ] ++ (pkgs.lib).optional (flags.compiler-only) "") ++ (pkgs.lib).optional true "";
          };
        "ghcjs-dumparchive" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."ghcjs" or (errorHandler.buildDepError "ghcjs"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            ];
          buildable = if flags.compiler-only then false else true;
          hsSourceDirs = [ "utils" ];
          mainPath = ([
            "dumpArchive.hs"
            ] ++ (pkgs.lib).optional (flags.compiler-only) "") ++ (pkgs.lib).optional (system.isWindows) "";
          };
        };
      tests = {
        "test" = {
          depends = [
            (hsPkgs."base" or (errorHandler.buildDepError "base"))
            (hsPkgs."process" or (errorHandler.buildDepError "process"))
            (hsPkgs."network" or (errorHandler.buildDepError "network"))
            (hsPkgs."aeson" or (errorHandler.buildDepError "aeson"))
            (hsPkgs."test-framework" or (errorHandler.buildDepError "test-framework"))
            (hsPkgs."test-framework-hunit" or (errorHandler.buildDepError "test-framework-hunit"))
            (hsPkgs."HUnit" or (errorHandler.buildDepError "HUnit"))
            (hsPkgs."filepath" or (errorHandler.buildDepError "filepath"))
            (hsPkgs."text" or (errorHandler.buildDepError "text"))
            (hsPkgs."transformers" or (errorHandler.buildDepError "transformers"))
            (hsPkgs."lens" or (errorHandler.buildDepError "lens"))
            (hsPkgs."random" or (errorHandler.buildDepError "random"))
            (hsPkgs."time" or (errorHandler.buildDepError "time"))
            (hsPkgs."bytestring" or (errorHandler.buildDepError "bytestring"))
            (hsPkgs."deepseq" or (errorHandler.buildDepError "deepseq"))
            (hsPkgs."unordered-containers" or (errorHandler.buildDepError "unordered-containers"))
            (hsPkgs."shelly" or (errorHandler.buildDepError "shelly"))
            (hsPkgs."data-default" or (errorHandler.buildDepError "data-default"))
            (hsPkgs."yaml" or (errorHandler.buildDepError "yaml"))
            (hsPkgs."optparse-applicative" or (errorHandler.buildDepError "optparse-applicative"))
            (hsPkgs."directory" or (errorHandler.buildDepError "directory"))
            (hsPkgs."http-types" or (errorHandler.buildDepError "http-types"))
            (hsPkgs."warp" or (errorHandler.buildDepError "warp"))
            (hsPkgs."wai" or (errorHandler.buildDepError "wai"))
            (hsPkgs."wai-extra" or (errorHandler.buildDepError "wai-extra"))
            (hsPkgs."wai-app-static" or (errorHandler.buildDepError "wai-app-static"))
            (hsPkgs."wai-websockets" or (errorHandler.buildDepError "wai-websockets"))
            (hsPkgs."websockets" or (errorHandler.buildDepError "websockets"))
            (hsPkgs."webdriver" or (errorHandler.buildDepError "webdriver"))
            (hsPkgs."lifted-base" or (errorHandler.buildDepError "lifted-base"))
            ];
          buildable = true;
          modules = [ "Server" "Client" "Types" ];
          hsSourceDirs = [ "test" ];
          mainPath = [ "TestRunner.hs" ];
          };
        };
      };
    } // rec {
    src = (pkgs.lib).mkDefault ../../ycdh1fs3bms17v3mwvsvya8j3jlp85l5-configured-ghcjs-src;
    }