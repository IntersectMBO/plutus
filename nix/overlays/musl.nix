self: super: {
  glibc = super.glibc.overrideAttrs (old: {
    # See https://github.com/NixOS/nixpkgs/pull/71480, should be fixed in future nixpkgs
    NIX_CFLAGS_COMPILE = if super.stdenv.hostPlatform.isMusl then
      ((if old.NIX_CFLAGS_COMPILE != null then old.NIX_CFLAGS_COMPILE else []) ++ ["-Wno-error=attribute-alias" "-Wno-error=stringop-truncation"])
      else old.NIX_CFLAGS_COMPILE;
  });
  python37 = super.python37.override {
    packageOverrides = self: super: {
      cython = super.cython.overridePythonAttrs (old: {
        # TODO Cython tests for unknown reason hang with musl. Remove when that's fixed.
        # See https://github.com/nh2/static-haskell-nix/issues/6#issuecomment-421852854
        doCheck = false;
      });
      pyopenssl = super.pyopenssl.overridePythonAttrs (old: { doCheck = false; });
    };
  };
}
