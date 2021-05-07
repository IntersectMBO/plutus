echo Marlowe workflow

CONFIG=/home/jann/plutus/plutus-pab/plutus-pab.yaml
COMPANION=/home/jann/plutus/dist-newstyle/build/x86_64-linux/ghc-8.10.4.20210212/marlowe-0.1.0.0/x/marlowe-companion-app/build/marlowe-companion-app/marlowe-companion-app
MARLOWE=/home/jann/plutus/dist-newstyle/build/x86_64-linux/ghc-8.10.4.20210212/marlowe-0.1.0.0/x/marlowe-app/build/marlowe-app/marlowe-app

echo Creating wallet companion for wallet $WALLET

COMPANIONID=$(curl -H "Content-Type: application/json" -d "{\"caID\": {\"contractPath\":\"$COMPANION\"}, \"caWallet\": {\"getWallet\": $WALLET}}" http://localhost:9080/api/new/contract/activate | jq -r '.unContractInstanceId')

echo Creating marlowe contract for wallet $WALLET

MARLOWEID=$(curl -H "Content-Type: application/json" -d "{\"caID\": {\"contractPath\":\"$MARLOWE\"}, \"caWallet\": {\"getWallet\": $WALLET}}" http://localhost:9080/api/new/contract/activate | jq -r '.unContractInstanceId')

sleep 5

echo Calling endpoint "create" on marlowe contract $MARLOWEID for PKH $PUBKEYHASH

curl -H "Content-Type: application/json" -d "[[[{\"unTokenName\":\"Investor\"},{\"getPubKeyHash\":\"$PUBKEYHASH\"}],[{\"unTokenName\":\"Issuer\"},{\"getPubKeyHash\":\"$PUBKEYHASH\"}]],{\"when\":[{\"then\":{\"token\":{\"token_name\":\"\",\"currency_symbol\":\"\"},\"to\":{\"party\":{\"role_token\":\"Issuer\"}},\"then\":{\"when\":[{\"then\":{\"token\":{\"token_name\":\"\",\"currency_symbol\":\"\"},\"to\":{\"party\":{\"role_token\":\"Investor\"}},\"then\":\"close\",\"pay\":20,\"from_account\":{\"role_token\":\"Issuer\"}},\"case\":{\"party\":{\"role_token\":\"Issuer\"},\"of_token\":{\"token_name\":\"\",\"currency_symbol\":\"\"},\"into_account\":{\"role_token\":\"Issuer\"},\"deposits\":20}}],\"timeout_continuation\":\"close\",\"timeout\":26936589},\"pay\":10,\"from_account\":{\"role_token\":\"Investor\"}},\"case\":{\"party\":{\"role_token\":\"Investor\"},\"of_token\":{\"token_name\":\"\",\"currency_symbol\":\"\"},\"into_account\":{\"role_token\":\"Investor\"},\"deposits\":10}}],\"timeout_continuation\":\"close\",\"timeout\":26936589}]" http://localhost:9080/api/new/contract/instance/${MARLOWEID}/endpoint/create

echo Waiting for everything to settle

sleep 25

echo Observable state of companion contract $COMPANIONID

curl http://localhost:9080/api/new/contract/instance/${COMPANIONID}/status | jq .cicCurrentState.observableState
