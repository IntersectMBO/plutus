{ pkgs ? (import <nixpkgs> {}) }:

let
    purtySrc = pkgs.fetchgit {
      url = "https://gitlab.com/joneshf/purty.git";
      rev = "74356b0be91dc2eaaf53eb63703f64f147ccfb45";
      sha256 = "1zccmb7vc2vwddsmdgc0xdkj06jskmh5ggf1szzb721src4v0c83";
    };
    packages = (import ./packages.nix { inherit pkgs; }).override {
        overrides = super: self: {
            # we need to fix hfsevents however we don't want to force it to be built in linux so we must add this conditional in
            hfsevents = if pkgs.stdenv.isDarwin then (super.callPackage ./hfsevents.nix {inherit (pkgs.darwin.apple_sdk.frameworks) Cocoa CoreServices;}) else "";
            # purescript needs to allow newer deps (jailbreak) so we have this override
            purescript = (super.callPackage ./purescript.nix {});
        };
    };
in
    with packages; mkDerivation {
      pname = "purty";
      version = "4.4.2";
      src = purtySrc;
      isLibrary = true;
      isExecutable = true;
      libraryHaskellDepends = [
        base bytestring componentm dhall optparse-applicative purescript
        rio text
      ];
      libraryToolDepends = [ hpack ];
      executableHaskellDepends = [ base ];
      doHaddock = false;
      doCheck = false;
      preConfigure = "hpack";
      homepage = "https://github.com/joneshf/purty#readme";
      license = pkgs.stdenv.lib.licenses.bsd3;
    }