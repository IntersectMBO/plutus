rm -f ./primary.db
stack exec plutus-pab -- --config=./config.yaml migrate
stack exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/plutus-currency"
stack exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/plutus-atomic-swap"
stack exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/plutus-game"
stack exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/plutus-pay-to-wallet"
stack exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/prism-credential-manager"
stack exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/prism-mirror"
stack exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/prism-unlock-sto"
stack exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/prism-unlock-exchange"
stack exec plutus-pab -- --config=./config.yaml all-servers
