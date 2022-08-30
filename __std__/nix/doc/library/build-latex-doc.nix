{ inputs, cell }:
let 
  inherit (inputs.nixpkgs) lib;
in 
  { name, description, src, texFiles ? null, withAgda ? false, agdaFile ? "" }:
    
    cell.library.build-latex {

      inherit name;
      inherit description;
      inherit texFiles;

      src = cell.library.filter-latex-sources src;

      buildInputs = lib.optionals withAgda [ 
        inputs.cells.toolchain.packages.agda-with-stdlib
      ];

      texInputs = {
        inherit (inputs.nixpkgs.texlive)
          acmart
          bibtex biblatex
          collection-bibtexextra
          collection-fontsextra
          collection-fontsrecommended
          collection-latex
          collection-latexextra
          collection-luatex
          collection-mathscience
          scheme-small;
      };

      preBuild = lib.optionalString withAgda ''
        agda --latex ${agdaFile} --latex-dir .
      '';
      
      meta = with lib; {
        inherit description;
        license = licenses.asl20;
      };
    }