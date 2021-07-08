#!/bin/bash

# Run in plutus/plutus-pab directory

echo Marlowe ZeroCouponBond

killall plutus-pab


rm -rf pab-core.db* && \
  cabal exec plutus-pab migrate && \
  cabal exec plutus-pab contracts install -- --path /Users/nau/projects/iohk/plutus/dist-newstyle/build/x86_64-osx/ghc-8.10.2.20201118/marlowe-0.1.0.0/x/marlowe-app/build/marlowe-app/marlowe-app && \
  cabal exec plutus-pab contracts install -- --path /Users/nau/projects/iohk/plutus/dist-newstyle/build/x86_64-osx/ghc-8.10.2.20201118/marlowe-0.1.0.0/x/marlowe-follow-app/build/marlowe-follow-app/marlowe-follow-app

nohup cabal exec plutus-pab all-servers &> /dev/null 2>&1 &

sleep 6

echo Activate W1 contract
echo

instanceId1=$(curl -s -H "Content-Type: application/json" \
  -d '{"caID": {"contractPath":"/Users/nau/projects/iohk/plutus/dist-newstyle/build/x86_64-osx/ghc-8.10.2.20201118/marlowe-0.1.0.0/x/marlowe-app/build/marlowe-app/marlowe-app"}, "caWallet": {"getWallet": 1}}' \
  http://localhost:9080/api/new/contract/activate | jq -r '.unContractInstanceId')

echo "Contract W1 $instanceId1"
echo

echo
echo Activate W2 follow contract
echo

followId=$(curl -s -H "Content-Type: application/json" \
  -d '{"caID": {"contractPath":"/Users/nau/projects/iohk/plutus/dist-newstyle/build/x86_64-osx/ghc-8.10.2.20201118/marlowe-0.1.0.0/x/marlowe-follow-app/build/marlowe-follow-app/marlowe-follow-app"}, "caWallet": {"getWallet": 1}}' \
  http://localhost:9080/api/new/contract/activate | jq -r '.unContractInstanceId')

sleep 3


# set -o xtrace

curl -s -H "Content-Type: application/json" -d '[[], {"timeout":300,"when":[{"then":{"to":{"party":{"pk_hash":"39f713d0a644253f04529421b9f51b9b08979d08295959c4f3990ee617f5139f"}},"then":{"timeout":600,"when":[{"then":"close","case":{"deposits":1000,"party":{"pk_hash":"39f713d0a644253f04529421b9f51b9b08979d08295959c4f3990ee617f5139f"},"of_token":{"currency_symbol":"","token_name":""},"into_account":{"pk_hash":"21fe31dfa154a261626bf854046fd2271b7bed4b6abe45aa58877ef47f9721b9"}}}],"timeout_continuation":"close"},"token":{"currency_symbol":"","token_name":""},"from_account":{"pk_hash":"21fe31dfa154a261626bf854046fd2271b7bed4b6abe45aa58877ef47f9721b9"},"pay":850},"case":{"deposits":850,"party":{"pk_hash":"21fe31dfa154a261626bf854046fd2271b7bed4b6abe45aa58877ef47f9721b9"},"of_token":{"currency_symbol":"","token_name":""},"into_account":{"pk_hash":"21fe31dfa154a261626bf854046fd2271b7bed4b6abe45aa58877ef47f9721b9"}}}],"timeout_continuation":"close"}]' \
  "http://localhost:9080/api/new/contract/instance/${instanceId1}/endpoint/create"

sleep 5

echo
echo Status
echo

curl -s "http://localhost:9080/api/new/contract/instance/${instanceId1}/status" | jq '.cicCurrentState.observableState'

sleep 3

echo
echo "Contract W2 follow $followId"
echo


curl -s -H "Content-Type: application/json" -d '{"rolesCurrency":{"unCurrencySymbol":""},"rolePayoutValidatorHash":"edb912810cdc518e698a8b2da6b5d8e1d1ef2916396dde2fe6c0611f62bda3ff"}' \
  "http://localhost:9080/api/new/contract/instance/${followId}/endpoint/follow"


# exit

echo
echo Deposit W1 850
echo

curl -s -H "Content-Type: application/json" -d '[{"rolesCurrency":{"unCurrencySymbol":""},"rolePayoutValidatorHash":"edb912810cdc518e698a8b2da6b5d8e1d1ef2916396dde2fe6c0611f62bda3ff"},null,[{"that_deposits":850,"input_from_party":{"pk_hash":"21fe31dfa154a261626bf854046fd2271b7bed4b6abe45aa58877ef47f9721b9"},"of_token":{"currency_symbol":"","token_name":""},"into_account":{"pk_hash":"21fe31dfa154a261626bf854046fd2271b7bed4b6abe45aa58877ef47f9721b9"}}]]' \
  "http://localhost:9080/api/new/contract/instance/${instanceId1}/endpoint/apply-inputs"

sleep 5

echo
echo Status W1
echo

curl "http://localhost:9080/api/new/contract/instance/${instanceId1}/status" | jq '.cicCurrentState.observableState'

echo
echo Status W2 follow
echo

curl "http://localhost:9080/api/new/contract/instance/${followId}/status" # | jq '.cicCurrentState.observableState'
echo "curl http://localhost:9080/api/new/contract/instance/${followId}/status"


echo
echo "W1 funds"
echo

curl http://localhost:9081/1/total-funds

sleep 5

echo
echo Activate W2 contract
echo

instanceId3=$(curl -s -H "Content-Type: application/json" \
  -d '{"caID": {"contractPath":"/Users/nau/projects/iohk/plutus/dist-newstyle/build/x86_64-osx/ghc-8.10.2.20201118/marlowe-0.1.0.0/x/marlowe-app/build/marlowe-app/marlowe-app"}, "caWallet": {"getWallet": 2}}' \
  http://localhost:9080/api/new/contract/activate | jq -r '.unContractInstanceId')

echo
echo "Contract W2 $instanceId3"
echo

# slot=$(curl -s http://localhost:9081/1/wallet-slot | jq -r '.getSlot')

sleep 5

echo
echo Status W2
echo

curl -s "http://localhost:9080/api/new/contract/instance/${instanceId3}/status" | jq '.cicCurrentState.observableState'

sleep 5

echo
echo Deposit W2 1000
echo

curl -s -H "Content-Type: application/json" -d '[{"rolesCurrency":{"unCurrencySymbol":""},"rolePayoutValidatorHash":"edb912810cdc518e698a8b2da6b5d8e1d1ef2916396dde2fe6c0611f62bda3ff"}, null, [{"that_deposits":1000,"input_from_party":{"pk_hash":"39f713d0a644253f04529421b9f51b9b08979d08295959c4f3990ee617f5139f"},"of_token":{"currency_symbol":"","token_name":""},"into_account":{"pk_hash":"21fe31dfa154a261626bf854046fd2271b7bed4b6abe45aa58877ef47f9721b9"}}]]' \
  "http://localhost:9080/api/new/contract/instance/${instanceId3}/endpoint/apply-inputs"

sleep 5

echo
echo Status W2 follow
echo

curl -s "http://localhost:9080/api/new/contract/instance/${followId}/status" | jq '.cicCurrentState.observableState'


echo
echo Status W2
echo

curl -s "http://localhost:9080/api/new/contract/instance/${instanceId3}/status" | jq '.cicCurrentState.observableState'

echo
echo
echo "W2 funds"
echo

curl -s http://localhost:9081/2/total-funds

sleep 5

echo
echo DONE

echo
echo "W1 funds"
echo

curl -s http://localhost:9081/1/total-funds

echo
echo
echo "W2 funds"
echo
curl -s http://localhost:9081/2/total-funds
echo
