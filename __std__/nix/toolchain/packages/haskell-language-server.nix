{ inputs, cell }:

cell.packages.todo-derivation


# hlsProject = haskell-nix.cabalProject' {
#   # See https://github.com/haskell/haskell-language-server/issues/411.
#   # We want to use stylish-haskell, hlint, and implicit-hie as standalone tools
#   # *and* through HLS. But we need to have consistent versions in both cases,
#   # otherwise e.g. you could format the code in HLS and then have the CI
#   # complain that it's wrong
#   #
#   # The solution we use here is to:
#   # a) Where we care (mostly just formatters), constrain the versions of
#   #    tools which HLS uses explicitly
#   # b) Pull out the tools themselves from the HLS project so we can use
#   #    them elsewhere
#   cabalProjectLocal = ''
#     constraints: stylish-haskell==0.13.0.0, hlint==3.2.8
#   '';
#   src = sources.haskell-language-server;
#   inherit compiler-nix-name;
#   modules = [{
#     # See https://github.com/haskell/haskell-language-server/pull/1382#issuecomment-780472005
#     packages.ghcide.flags.ghc-patched-unboxed-bytecode = true;
#   }];
# };