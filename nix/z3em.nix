
# TODO: We will move this into the upstream nixpkgs (iohk and nix organizations) and then we can remove it
{ pkgs, lib, stdenv, fetchFromGitHub, python, fixDarwinDylibNames, sources }:

let
  extraFlags = "--staticbin --staticlib --x86";
in
pkgs.buildEmscriptenPackage rec {
  name = "z3";
  version = "4.8.6";

  src = fetchFromGitHub {
    owner  = "Z3Prover";
    repo   = name;
    rev = "4c0db00a7b37d277e3a703794fad31e52adfc455";
    sha256 = "1m03cx7nay76328n88qs4awx0i6j2amwwm04l23ks1vjnv785nf2";
  };

  buildInputs = [ python fixDarwinDylibNames ];
  propagatedBuildInputs = [ python.pkgs.setuptools ];
  enableParallelBuilding = true;

  configurePhase = ''
    HOME=$TMPDIR
    emconfigure ${python.interpreter} scripts/mk_make.py --prefix=$out --python --pypkgdir=$out/${python.sitePackages} ${extraFlags}
    sed -i 's/-D_LINUX_//g' build/config.mk
  '';

  buildPhase = ''
    emmake make -C build
    cp ./build/z3 ./build/z3.bc
    emcc -s INVOKE_RUN=0 -O3 \
    -s MODULARIZE=1 \
    -s EXPORT_NAME='Z3' \
    -s STRICT=1 \
    -s ERROR_ON_UNDEFINED_SYMBOLS=1 \
    -s DISABLE_EXCEPTION_CATCHING=0 \
    -s ABORTING_MALLOC=0 \
    -s ALLOW_MEMORY_GROWTH=1 \
    -s EXPORTED_FUNCTIONS=["_main"] \
    -s EXTRA_EXPORTED_RUNTIME_METHODS=["FS"] \
    -l nodefs.js \
    -s WASM=1 \
    -s BINARYEN_ASYNC_COMPILATION=0 \
    ./build/z3.bc -o z3w.js
  '';

  checkPhase = ''
    echo "ignore checks"
    true
  '';

  installPhase = ''
    mkdir -p $out
    mv z3w.js $out/z3w.js
    mv z3w.wasm $out/z3w.wasm
  '';

  meta = {
    description = "A high-performance theorem prover and SMT solver";
    homepage    = "https://github.com/Z3Prover/z3";
    license     = stdenv.lib.licenses.mit;
    platforms   = stdenv.lib.platforms.x86_64;
    maintainers = [ stdenv.lib.maintainers.thoughtpolice ];
  };
}
