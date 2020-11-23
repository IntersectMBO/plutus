{ runCommand, nixpkgs-fmt, src }:

# Runs `nixpkgs-fmt --check` on ${src}. If nixpkgs-fmt
# reports that files need to be re-formatted details are
# written to `$out/nix-support/hydra-build-products`
runCommand "nixpkgs-fmt"
{
  buildInputs = [ nixpkgs-fmt ];
} ''
  set +e
  nixpkgs-fmt --check ${src} 2>&1 >nixpkgs-fmt.log

  if [ $? -ne 0 ]; then
    mkdir -p $out/nix-support
    cat nixpkgs-fmt.log > $out/nix-support/hydra-build-products
    echo "*** nixpkgs-fmt found files that haven't been formatted"
    echo "*** Please run \`nix-shell --run \"nixpkgs-fmt .\"\` and commit the changes"
    exit 1
  else
    echo 0 > $out
  fi
''
