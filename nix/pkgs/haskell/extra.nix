############################################################################
# Extra Haskell packages which we build with haskell.nix, but which aren't
# part of our project's package set. Normally we try and include packages 
# there (using 'extra-packages' in 'cabal.project'), in order to minimize 
# the amount of haskell.nix package sets we evaluate (which can take a while), 
# but these ones can't be included there for one reason or another.
############################################################################
{ stdenv
, lib
, haskell-nix
, fetchFromGitHub
, fetchFromGitLab
, index-state
, compiler-nix-name
, checkMaterialization
, buildPackages
}:
{
  # Can't be included in 'extra-packages' since it doesn't build with newer versions
  # of base. Maybe reconsider once 3.4 is out.
  cabal-install = haskell-nix.hackage-package {
    name = "cabal-install";
    version = "3.2.0.0";
    inherit compiler-nix-name index-state checkMaterialization;
    # Invalidate and update if you change the version or index-state
    plan-sha256 = "0m1h3hp95cflj28vhxyl1hl7k3frhx8f1mbkc8ry2dms603w2nrw";
  };
}
  //
  # We need to lift this let-binding out far enough, otherwise it can get evaluated several times!
  # Can't be included in 'extra-packages' since it's not on hackage yet. Reconsider
  # once it's on hackage.
(
  let hspkgs = haskell-nix.cabalProject {
    src = fetchFromGitHub {
      owner = "haskell";
      repo = "haskell-language-server";
      rev = "0.8.0";
      sha256 = "0p6fqs07lajbi2g1wf4w3j5lvwknnk58n12vlg48cs4iz25gp588";
      fetchSubmodules = true;
    };
    inherit compiler-nix-name checkMaterialization;
    # Plan issues with the benchmarks, can try removing later
    configureArgs = "--disable-benchmarks";
    # Invalidate and update if you change the version
    plan-sha256 =
      # See https://github.com/input-output-hk/nix-tools/issues/97
      if stdenv.isLinux
      then "07p6z6jb87k8n0ihwxb8rdnjb7zddswds3pxca9dzsw47rd9czyd"
      else "1s3cn381945hrs1fchg6bbkcf3abi0miqzc30bgpbfj23a8lhj2q";
    modules = [{
      packages.ghcide.patches = [ ../../patches/ghcide_partial_iface.patch ];
    }];
  };
  in { inherit (hspkgs) haskell-language-server hie-bios implicit-hie; }
)
