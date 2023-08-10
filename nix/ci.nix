# This file is part of the IOGX template and is documented at the link below:
# https://www.github.com/input-output-hk/iogx#39-nixcinix

{ l, system, ... }:

{
  includeDefaultOutputs = false;


  includedPaths =
    l.optionals (system == "x86_64-linux" || system == "x86_64-darwin") [
      "packages"
      "devShells"
      "checks"
    ]

    ++ l.optionals (system == "x86_64-linux") [
      # Only build the latex documents on linux
      "documents"
    ]

    ++ l.optionals (system == "aarch64-darwin") [
      # Plausibly if things build on x86 darwin then they'll build on aarch darwin.
      # Se we only build roots and devshells on aarch to avoid overloading the builders.
      # Note: We can't build the 9.6 shell on aarch64-darwin
      # because of https://github.com/well-typed/cborg/issues/311
      "devShells.ghc8107"
      "devShells.ghc927"
      "packages.haskell-nix-project-roots-ghc8107"
      "packages.haskell-nix-project-roots-ghc927"
      "packages.haskell-nix-project-roots-ghc961"
    ];

}

