# We use some customized libiserv/remote-iserv/iserv-proxy
# instead of the ones provided by ghc. This is mostly due
# to being able to hack on them freely as needed.
#
# iserv is only relevant for template-haskell execution in
# a cross compiling setup.
{
  ghci         = ./ghci.nix;
  ghc-boot     = ./ghc-boot.nix;
  libiserv     = ./libiserv.nix;
  remote-iserv = ./remote-iserv.nix;
  iserv-proxy  = ./iserv-proxy.nix;
}
