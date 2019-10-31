self: super: {
  nix-gitignore = super.callPackage (super.fetchFromGitHub {
    owner = "siers";
    repo = "nix-gitignore";
    rev = "686b057f6c24857c8862c0ef15a6852caab809c7";
    sha256 = "1hv8jl7ppv0f8lnfx2qi2jmzc7b5yiy12yvd4waq9xmxhip1k7rb";
  }) { };
}
