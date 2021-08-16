self: super: {
  # nixpkgs-fmt 1.2.0 breaks indentation of code examples in comments
  nixpkgs-fmt = self.rustPlatform.buildRustPackage rec {
    pname = "nixpkgs-fmt";
    version = "1.1.0";

    src = self.fetchFromGitHub {
      owner = "nix-community";
      repo = pname;
      rev = "v${version}";
      sha256 = "1fb2mm1y2qb3imc48g2ad3rdbjlj326cggrc4hvdc0fb41vxinpp";
    };

    cargoSha256 = "1lsw6dwkjdwdqcx7gjsg2ndi4r79m8qyxgx7yz3al0iscwm7i645";
    meta = with self.lib; {
      description = "Nix code formatter for nixpkgs";
      homepage = "https://nix-community.github.io/nixpkgs-fmt";
      license = licenses.asl20;
      maintainers = with maintainers; [ zimbatm ];
    };
  };

  python3 = super.python3.override {
    packageOverrides = python-self: python-super: {
      # New version has much better citation styles
      sphinxcontrib-bibtex = python-super.sphinxcontrib-bibtex.overrideAttrs (oldAttrs: rec {
        version = "2.2.0";
        src = python-super.fetchPypi {
          inherit (oldAttrs) pname;
          inherit version;
          sha256 = "1cp3dj5bbl122d64i3vbqhjhfplnh1rwm9dw4cy9hxjd2lz8803m";
        };
      });
    };
  };
}
