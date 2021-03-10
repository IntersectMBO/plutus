{ runCommand, terraform, src }:

# Runs `terraform fmt -check` on ${src}. If it 
# reports that files need to be re-formatted details are
# written to `$out/nix-support/hydra-build-products`
runCommand "terraform-fmt"
{
  buildInputs = [ terraform ];
} ''
  set +e
  terraform fmt -recursive -check ${src} 2>&1 >terraform.log

  if [ $? -ne 0 ]; then
    mkdir -p $out/nix-support
    cat terraform.log > $out/nix-support/hydra-build-products
    echo "*** terraform fmt found files that haven't been formatted"
    echo "*** Please run \`nix-shell --run \"terraform fmt -recursive .\"\` and commit the changes"
    exit 1
  else
    echo 0 > $out
  fi
''
