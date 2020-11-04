# TODO: We will move this into the upstream nixpkgs (iohk and nix organizations) and then we can remove it
{ lib, stdenv, fetchFromGitHub, python, fixDarwinDylibNames, staticbin ? false }:

let
  extraFlags = lib.optionalString staticbin "--staticbin";
in
stdenv.mkDerivation rec {
  name = "z3";
  version = "4.8.6";

  src = fetchFromGitHub {
    owner = "Z3Prover";
    repo = name;
    rev = "4c0db00a7b37d277e3a703794fad31e52adfc455";
    sha256 = "1m03cx7nay76328n88qs4awx0i6j2amwwm04l23ks1vjnv785nf2";
  };

  buildInputs = [ python fixDarwinDylibNames ];
  propagatedBuildInputs = [ python.pkgs.setuptools ];
  enableParallelBuilding = true;

  configurePhase = ''
    ${python.interpreter} scripts/mk_make.py --prefix=$out --python --pypkgdir=$out/${python.sitePackages} ${extraFlags}
    cd build
  '';

  postInstall = ''
    mkdir -p $dev $lib $python/lib
    mv $out/lib/python*  $python/lib/
    mv $out/lib          $lib/lib
    mv $out/include      $dev/include
    ln -sf $lib/lib/libz3${stdenv.hostPlatform.extensions.sharedLibrary} $python/${python.sitePackages}/z3/lib/libz3${stdenv.hostPlatform.extensions.sharedLibrary}
  '';

  outputs = [ "out" "lib" "dev" "python" ];

  meta = {
    description = "A high-performance theorem prover and SMT solver";
    homepage = "https://github.com/Z3Prover/z3";
    license = stdenv.lib.licenses.mit;
    platforms = stdenv.lib.platforms.x86_64;
    maintainers = [ stdenv.lib.maintainers.thoughtpolice ];
  };
}
