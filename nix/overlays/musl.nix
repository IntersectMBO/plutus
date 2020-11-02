self: super:
let
  lib = super.lib;
  hostPlatform = super.stdenv.hostPlatform;
in
{
  glibc = super.glibc.overrideAttrs (old: lib.optionalAttrs hostPlatform.isMusl {
    # See https://github.com/NixOS/nixpkgs/pull/71480, should be fixed in future nixpkgs
    NIX_CFLAGS_COMPILE = (if old.NIX_CFLAGS_COMPILE != null then old.NIX_CFLAGS_COMPILE else [ ]) ++ [ "-Wno-error=attribute-alias" "-Wno-error=stringop-truncation" ];
  });

  python37 = super.python37.override {
    packageOverrides = self: super: {
      cython = super.cython.overridePythonAttrs (old: lib.optionalAttrs hostPlatform.isMusl {
        # TODO Cython tests for unknown reason hang with musl. Remove when that's fixed.
        # See https://github.com/nh2/static-haskell-nix/issues/6#issuecomment-421852854
        doCheck = false;
      });
      # The tests just seem to be broken with musl, it's unclear why
      pyopenssl = super.pyopenssl.overridePythonAttrs (old: lib.optionalAttrs hostPlatform.isMusl {
        doCheck = false;
      });
    };
  };

  # nixpkgs bug: musl cross is mis-detected
  openssl = super.openssl.overrideAttrs (old: lib.optionalAttrs hostPlatform.isMusl {
    configureScript = "./Configure linux-x86_64";
  });
}
