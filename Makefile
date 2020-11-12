default: secrets/nix-public-key-file
.PHONY: default

secrets:
	mkdir -p secrets

secrets/nix-public-key-file: secrets/nix-secret-key-file

secrets/nix-secret-key-file: secrets
	nix-store --generate-binary-cache-key vit-testnet-0 secrets/nix-secret-key-file secrets/nix-public-key-file
