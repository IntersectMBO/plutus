# Additional configuration for Agda environment. The `uplc` executable requires
# knowledge of the Agda standard library location and the metatheory source directory.
# This information is needed both inside the nix shell and by the upls exec at runtime.
{ repoRoot, inputs, pkgs, system, lib }:
{
  shellHookExports = ''
    export AGDA_STDLIB_SRC="${repoRoot.nix.agda-with-stdlib}/src"
    export PLUTUS_METHATHEORY_SRC="${../plutus-metatheory/src}"
  '';

  wrapProgramArgs = ''
    --set AGDA_STDLIB_SRC "${repoRoot.nix.agda-with-stdlib}/src" \
    --set PLUTUS_METHATHEORY_SRC "${../plutus-metatheory/src}"
  '';
}
