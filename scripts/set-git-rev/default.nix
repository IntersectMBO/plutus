{ pkgs, ghc, git-rev, stdenv }:

with pkgs.lib;

let
  # Wraps a haskell package derivation so that it has all dynamic
  # linking, development and doc files removed.
  #
  # Use file-embed to inject the git revision into all programs of
  # all derivation outputs.
  #
  # This is done by copying all files from the wrapped derivation
  # rather than with a package override. If an override were used, the
  # derivation would need to be rebuilt whenever git-rev changed.
  overrideGitRev = drvOut: let
    drvOutOutputs = drvOut.outputs or ["out"];
  in
    pkgs.runCommand (drvOut.pname + "-" + git-rev) {
      outputs  = drvOutOutputs;
      passthru = drvOut.drvAttrs
        // (drvOut.passthru or {})
        // { inherit git-rev; };
    }
    (concatMapStrings (output: ''
      cp -a "${drvOut.${output}}" "${"$"}${output}"
      chmod -R +w "${"$"}${output}"
      for prog in "${"$"}${output}"/bin/*; do
        ${setGitRev} "${git-rev}" "$prog" || true
      done
    '') drvOutOutputs);

  setGitRev = pkgs.runCommand "set-git-rev" {
    # https://github.com/NixOS/nixpkgs/issues/46814
    flags = optionalString stdenv.isDarwin "-liconv";
  } ''
    ${ghc.withPackages (ps: [ps.text ps.file-embed])}/bin/ghc $flags -o $out ${./set-git-rev.hs}
  '';
in
  overrideGitRev