# Prebuilt executables for GitHub releases: `uplc`, `plc`, `pir` and `plutus`
# as single files that run on any machine of the given platform, with no Nix
# and no other dependencies installed.
#
# - Linux: fully static binaries linked against musl, built with the
#   haskell.nix `musl64` cross project.
#
# - macOS: there is no static libSystem, so the binaries are static except for
#   the OS itself: every other C library (gmp, ffi, libsodium, secp256k1, blst,
#   libc++, ncurses, iconv) is linked in from `pkgsStatic`, and the result loads
#   nothing but /usr/lib/libSystem and system frameworks.
#
# Outputs (per system):
#
#   static-<exe>          the executable under bin/, usable with `nix run`.
#   release-executables   all of them as the files to attach to a release,
#                         named <exe>-<system>-ghc96.
#
# Hydra builds `release-executables` for x86_64-linux and aarch64-darwin, and
# scripts/interactive-release.sh fetches them from the cache when publishing.

{ pkgs, lib, project, system }:

let
  exes = [ "uplc" "plc" "pir" "plutus" ];

  ghc = "ghc96";

  inherit (pkgs.stdenv.hostPlatform) isLinux isDarwin isx86_64;

  # The systems with Hydra builders. Others get no static packages at all.
  supported = (isLinux && isx86_64) || isDarwin;

  # Directories holding static (.a only) builds of the C libraries the
  # executables would otherwise load as dylibs from the Nix store.
  staticLibDirs = with pkgs.pkgsStatic;
    map (l: "${lib.getLib l}/lib") [
      gmp # ghc-bignum
      libffi # rts
      libsodium-vrf # cardano-crypto-class
      secp256k1 # cardano-crypto-class
      libblst # cardano-crypto-class
      llvmPackages.libcxx # system-cxx-std-lib, pulled in by blst
      ncurses # haskeline
    ]
    ++ [ "${libiconv.dev}/lib" ]; # base; Apple's libiconv keeps its .a in dev

  # GHC puts `-L` directories given as GHC options on the link line before the
  # library directories of the packages it links, and ld64 takes the first
  # directory that has the library in either form, so listing the .a-only
  # directories first makes it link those instead of the dylibs.
  darwinProject = project.appendModule {
    modules = [{
      packages.plutus-executables.components.exes = lib.genAttrs exes (_: {
        configureFlags = map (dir: "--ghc-option=-L${dir}") staticLibDirs;
      });
    }];
  };

  # Strip the executable and check it is self-contained: any dylib still loaded
  # from the Nix store would make it fail on every other machine. $STRIP is the
  # stdenv's cctools strip, whose wrapper re-signs the binary as arm64 macOS
  # requires. (Do not add `binutils` here: on darwin that is GNU binutils,
  # whose strip corrupts Mach-O load commands.)
  selfContainedMacOsExe = exe: drv:
    pkgs.runCommandCC "${exe}-static"
      {
        passthru.exeName = exe;
      } ''
      mkdir -p $out/bin
      cp ${drv}/bin/${exe} $out/bin/
      chmod +w $out/bin/${exe}
      # The Haskell executable ships unstripped (140MB for uplc, 88MB stripped).
      $STRIP $out/bin/${exe}

      if otool -L $out/bin/${exe} | tail -n +2 | grep -q /nix/store; then
        echo "error: ${exe} still loads libraries from the Nix store:" >&2
        otool -L $out/bin/${exe} >&2
        exit 1
      fi
      $out/bin/${exe} --help > /dev/null
    '';

  hsPkgs =
    if isLinux then project.projectCross.musl64.hsPkgs
    else darwinProject.hsPkgs;

  staticExe = exe:
    let drv = hsPkgs.plutus-executables.components.exes.${exe}; in
    if isDarwin then selfContainedMacOsExe exe drv else drv;

  static-executables =
    lib.listToAttrs (map (exe: lib.nameValuePair "static-${exe}" (staticExe exe)) exes);

  assetName = exe: "${exe}-${system}-${ghc}";

  # Names used by earlier release scripts; kept as aliases.
  aliases = lib.optionalAttrs isLinux
    (lib.listToAttrs (map (exe: lib.nameValuePair "musl64-${exe}" (staticExe exe)) exes));

  # The assets are the bare binaries. On Linux they are stripped and
  # upx-compressed as the release script always did; on macOS they are already
  # stripped (and upx does not support arm64 Mach-O).
  release-executables =
    pkgs.runCommand "release-executables-${system}"
      {
        nativeBuildInputs =
          lib.optionals isLinux [ pkgs.buildPackages.binutils pkgs.buildPackages.upx ];
      }
      (''
        mkdir -p $out
      '' + lib.concatMapStrings
        (exe: ''
          cp ${staticExe exe}/bin/${exe} $out/${assetName exe}
        '' + lib.optionalString isLinux ''
          chmod +w $out/${assetName exe}
          strip $out/${assetName exe}
          upx -9 $out/${assetName exe}
        '')
        exes);

in

lib.optionalAttrs supported
  (static-executables // { inherit release-executables; } // aliases)
