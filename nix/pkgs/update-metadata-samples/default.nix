{ writeScriptBin, runtimeShell, curl }:
let
  metadataQueryPayload1 = {
    subjects = [
      "44b57ee30cdb55829d0a5d4f046baef078f1e97a7f21b62d75f8e96ea139c35f"
      "7f71940915ea5fe85e840f843c929eba467e6f050475bad1f10b9c274d1888c0"
    ];
  };

  metadataQueryPayload2 = {
    subjects = [
      "44b57ee30cdb55829d0a5d4f046baef078f1e97a7f21b62d75f8e96ea139c35f"
      "7f71940915ea5fe85e840f843c929eba467e6f050475bad1f10b9c274d1888c0"
    ];
    properties = [
      "name"
      "description"
    ];
  };
in
writeScriptBin "update-metadata-samples" ''
  #!${runtimeShell}
  set -eou pipefail

  SERVER=https://api.cardano.org/staging
  SUBJECT=7f71940915ea5fe85e840f843c929eba467e6f050475bad1f10b9c274d1888c0
  DATA_DIR=plutus-scb/test/Cardano/Metadata

  ${curl}/bin/curl -o $DATA_DIR/subject_response1.json $SERVER/metadata/$SUBJECT

  for PROPERTY in name owner preImage description
  do
    ${curl}/bin/curl -o $DATA_DIR/property_$PROPERTY.json $SERVER/metadata/$SUBJECT/properties/$PROPERTY
  done

  ${curl}/bin/curl -X POST -o $DATA_DIR/query_response1.json $SERVER/metadata/query \
    -H 'Content-Type: application/json' \
    -d '${builtins.toJSON metadataQueryPayload1}'

  ${curl}/bin/curl -X POST -o $DATA_DIR/query_response2.json $SERVER/metadata/query \
    -H 'Content-Type: application/json' \
    -d '${builtins.toJSON metadataQueryPayload2}'
''
