
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
    -s EXPORTED_FUNCTIONS=["_Z3_eval_smtlib2_string", "_Z3_mk_config", "_Z3_mk_context", "_Z3_del_config", "_Z3_del_context", "_Z3_mk_solver", "_Z3_solver_push", "_Z3_solver_pop", "_Z3_solver_reset", "_Z3_solver_inc_ref", "_Z3_solver_dec_ref", "_Z3_model_inc_ref", "_Z3_model_dec_ref", "_Z3_mk_string_symbol", "_Z3_mk_const", "_Z3_mk_int_sort", "_Z3_solver_assert", "_Z3_solver_get_model", "_Z3_mk_const", "_Z3_solver_check", "_Z3_model_to_string", "_Z3_model_get_const_interp", "_Z3_ast_to_string", "_Z3_func_decl_to_string", "_Z3_mk_func_decl", "_Z3_mk_app", "_Z3_mk_int", "_Z3_mk_string", "_Z3_mk_string_sort", "_Z3_mk_true", "_Z3_mk_false", "_Z3_mk_bool_sort", "_Z3_mk_lt", "_Z3_mk_le", "_Z3_mk_gt", "_Z3_mk_ge", "_Z3_mk_eq", "_Z3_mk_add", "_Z3_mk_mul", "_Z3_mk_sub", "_Z3_mk_not", "_Z3_mk_and", "_Z3_mk_or", "_Z3_mk_ite"] \
    -s EXTRA_EXPORTED_RUNTIME_METHODS=["ccall", "cwrap", "allocateUTF8", "writeAsciiToMemory"] \
    -l nodefs.js \
    -s WASM=1 \
    -s BINARYEN_ASYNC_COMPILATION=1 \
    -s ENVIRONMENT=web,worker \
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
