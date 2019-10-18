{ pkgs ? (import <nixpkgs> {}) }:

let
    purtySrc = pkgs.fetchgit {
      url = "https://gitlab.com/joneshf/purty.git";
      rev = "3c073e1149ecdddd01f1d371c70d5b243d743bf2";
      sha256 = "0j8z9661anisp4griiv5dfpxarfyhcfb15yrd2k0mcbhs5nzhni0";
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