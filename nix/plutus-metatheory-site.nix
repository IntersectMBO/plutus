{ repoRoot, inputs, pkgs, system, lib }:

let

  # Doing this in two derivations so the call to agda is cached, since
  # that's very slow. Makes it easier to iterate on the site build.
  plutus-metatheory-agda-html = pkgs.stdenv.mkDerivation {
    name = "plutus-metatheory-doc";
    src = inputs.self + /plutus-metatheory;
    buildInputs = [ repoRoot.nix.agda-with-stdlib ];

    # Because of a quirk with jekyll, the _layouts folder must be in the same
    # directory as the source folder.
    buildPhase = ''
      mkdir $out
      cp -R ${inputs.self + /plutus-metatheory/html/_layouts} $out
      agda --html --html-highlight=auto --html-dir="$out" "src/index.lagda.md"
    '';
    dontInstall = true;
  };

  plutus-metatheory-site = pkgs.runCommand "plutus-metatheory-site"
    {
      buildInputs = [ pkgs.jekyll ];
    }
    ''
      mkdir "$out"
      # Disable the disk cache otherwise it tries to write to the source
      jekyll build \
        --disable-disk-cache \
        -s ${plutus-metatheory-agda-html} \
        -d "$out"
    '';
in

plutus-metatheory-site
