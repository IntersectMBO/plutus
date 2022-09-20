{ inputs, cell }:

let pkgs = cell.library.pkgs; in

pkgs.rustPlatform.buildRustPackage rec {

  pname = "nixpkgs-fmt";

  # nixpkgs-fmt 1.2.0 breaks indentation of code examples in comments
  version = "1.1.0";

  src = pkgs.fetchFromGitHub {
    owner = "nix-community";
    repo = pname;
    rev = "v${version}";
    sha256 = "1fb2mm1y2qb3imc48g2ad3rdbjlj326cggrc4hvdc0fb41vxinpp";
  };

  cargoSha256 = "1lsw6dwkjdwdqcx7gjsg2ndi4r79m8qyxgx7yz3al0iscwm7i645";

  meta = with pkgs.lib; {
    description = "Nix code formatter for nixpkgs";
    homepage = "https://nix-community.github.io/nixpkgs-fmt";
    license = licenses.asl20;
    maintainers = with maintainers; [ zimbatm ];
  };
}
