# Copied from nixpkgs, remove when we hit 20.09

{ stdenv, mkDerivation, fetchFromGitHub, ghcWithPackages }:

mkDerivation rec {
  pname = "standard-library";
  version = "1.4";

  src = fetchFromGitHub {
    repo = "agda-stdlib";
    owner = "agda";
    rev = "3922be6a77cb925ac596010d882349aae1e45ff3";
    # rev = "v${version}";
    sha256 = "1agnax3s1v3q3z0psd4pbq3pvnhvqi9lpcgm878iaf1ch1aqnqx4";
  };

  nativeBuildInputs = [ (ghcWithPackages (self : [ self.filemanip ])) ];
  preConfigure = ''
    runhaskell GenerateEverything.hs
  '';

  meta = with stdenv.lib; {
    homepage = "https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary";
    description = "A standard library for use with the Agda compiler";
    license = stdenv.lib.licenses.mit;
    platforms = stdenv.lib.platforms.unix;
    maintainers = with maintainers; [ jwiegley mudri alexarice turion ];
  };
}
