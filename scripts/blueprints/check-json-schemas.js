#!/usr/bin/env node

// Remember to run 'npm install' from inside this directory first. 

const log = console.log;
const acmeGolden = "../../plutus-tx-plugin/test/Blueprint/Acme.golden.json";
const Ajv2020 = require("ajv/dist/2020");
const ajv = new Ajv2020({ strict: true, allErrors: true });

ajv.addMetaSchema(require("./CIP-57/plutus-blueprint.json"));
ajv.addMetaSchema(require("./CIP-57/plutus-blueprint-argument.json"));
ajv.addMetaSchema(require("./CIP-57/plutus-blueprint-parameter.json"));
ajv.addMetaSchema(require("./CIP-57/plutus-builtin.json"));
ajv.addMetaSchema(require("./CIP-57/plutus-data.json"));
ajv.addKeyword({ keyword: "example", type: "string" });
ajv.addKeyword({ keyword: "dataType" });

log("Validating " + acmeGolden);

const res = ajv.validateSchema(require(acmeGolden));

if (res) {
  log("Data is valid");
  process.exit(0);
} else {
  log("Data is invalid:");
  console.dir(ajv.errors);
  process.exit(1);
}
