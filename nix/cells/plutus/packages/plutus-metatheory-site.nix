{ inputs, cell }:

let
  # Doing this in two derivations so the call to agda is cached, since
  # that's very slow. Makes it easier to iterate on the site build.
  plutus-metatheory-agda-html = cell.library.pkgs.stdenv.mkDerivation {
    name = "plutus-metatheory-doc";
    src = inputs.self + /plutus-metatheory;
    buildInputs = [ cell.packages.agda-with-stdlib ];
    buildPhase = ''
      mkdir "$out"
      agda --html --html-highlight=auto --html-dir="$out" "src/index.lagda.md"
    '';
    dontInstall = true;
  };
  plutus-metatheory-site = cell.library.pkgs.runCommand "plutus-metatheory-site"
    {
      buildInputs = [ cell.library.pkgs.jekyll ];
    }
    ''
      mkdir "$out"
      # disable the disk cache otherwise it tries to write to the source
      jekyll build \
        --disable-disk-cache \
        -s ${plutus-metatheory-agda-html} \
        -d "$out"
    '';
in
plutus-metatheory-site
