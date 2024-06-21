# Documentation Traceability Report

## Version

Version 1.1

## Authors

Romain Soulat <romain.soulat@iohk.io>

## Table of Contents

- [Revision History](#revision-history)
- [References](#references)
- [Introduction](#introduction)
- [Parameter traceability](#parameter-traceability)
- [Documentation traceability](#documentation-traceability)

## Revision History

| Version | Date | Author | Changes |
| --- | --- | --- | --- |
| 1.0 | 2024-05-13 | Romain Soulat | Initial version |
| 1.1 | 2024-05-14 | Romain Soulat | Updated with new version of defaultConstitution.json |

## References

- Interim Constitution
  - SHA 256: `7b4e7c896a8b48b1f1109c92934f1858ae7941183e223a35bf4e9a8e`
  - URL: <https://docs.google.com/document/d/1GwI_6qzfTa5V_BeEY4f-rZNhbfA8lXon/>

- CDDL description of the protocol parameters
  - SHA 256: `5c712c432227acff7e4c26576343fcfe966a66dd0a09db1e61821b55283da47f`
  - URL: <https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl>

- JSON used to generate the constitution script
  - SHA 256: `9dfa556ee6321ed389444f186ce9d26c637359749be11d516c944711c8ef5af7`
  - URL: <https://github.com/IntersectMBO/plutus/blob/master/cardano-constitution/data/defaultConstitution.json>

## Introduction

This document provides a traceability between the Interim Constitution, the cddl description of the protocol parameters and the JSON/TSV used to generate the constitution script.

## Parameter traceability

The Interim Constitution is a human readable document that describes the protocol parameters. The CDDL description of the protocol parameters is a machine readable document that describes the protocol parameters.

| Interim Constitution Parameter Name | CDDL Parameter number | CDDL Parameter name (in comments) |
|---|---|---|
| txFeePerByte | 0 | min fee a |
| txFeeFixed | 1 | min fee b |
| maxBlockBodySize | 2 | max block body size |
| maxTxSize | 3 | max transaction size |
| maxBlockHeaderSize | 4 | max block header size |
| stakeAddressDeposit | 5 | key deposit |
| stakePoolDeposit | 6 | pool deposit |
| poolRetireMaxEpoch | 7 | maximum epoch |
| stakePoolTargetNum | 8 | n_opt: desired number of stake pool |
| poolPledgeInfluence | 9 | pool pledge influence |
| monetaryExpansion | 10 | expansion rate |
| treasuryCut | 11 | treasury growth rate |
| BLANK NO PARAMETER | 12 | BLANK NO PARAMETER |
| BLANK NO PARAMETER | 13 | BLANK NO PARAMETER |
| BLANK NO PARAMETER | 14 | BLANK NO PARAMETER |
| BLANK NO PARAMETER | 15 | BLANK NO PARAMETER |
| minPoolCost | 16 | min pool cost |
| utxoCostPerByte | 17 | ada per utxo byte |
| costModels | 18 | cost models for script language |
| executionUnitPrices | 19 | execution costs |
| executionUnitPrices[priceMemory] | 19.0 | execution costs mem|
| executionUnitPrices[priceSteps] | 19.1 | execution costs steps|
| maxTxExecutionUnits | 20 | max tx ex units |
| maxTxExecutionUnits[mem] | 20.0 | |
| maxTxExecutionUnits[steps] | 20.1 | |
| maxBlockExecutionUnits | 21 | max block ex units |
| maxBlockExecutionUnits[mem] | 21.0 | |
| maxBlockExecutionUnits[steps] | 21.1 | |
| maxValueSize | 22 | max value size |
| collateralPercentage | 23 | collateral percentage |
| maxCollateralInputs | 24 | max collateral inputs |
| poolVotingThresholds | 25 | pool voting thresholds |
| poolVotingThresholds[pvtMotionNoConfidence] | 25.0 | motion no confidence |
| poolVotingThresholds[pvtCommitteeNormal] | 25.1 | committee normal |
| poolVotingThresholds[pvtCommitteeNoConfidence] | 25.2 | committee no conficence |
| poolVotingThresholds[pvtHardForkInitiation] | 25.3 | hard fork initiation |
| poolVotingThresholds[pvtPPSecurityGroup] | 25.4 | security relevant parameter voting threshold|
| dRepVotingThresholds | 26 | DRep voting threshold |
| dRepVotingThresholds[dvtMotionNoConfidence] | 26.0 | motion no confidence |
| dRepVotingThresholds[dvtCommitteeNormal] | 26.1 | committee normal |
| dRepVotingThresholds[dvtCommitteeNoConfidence] | 26.2 | committee no confidence |
| dRepVotingThresholds[dvtUpdateToConstitution] | 26.3 | update constitution |
| dRepVotingThresholds[dvtHardForkInitiation] | 26.4 | hard fork initiation |
| dRepVotingThresholds[dvtPPNetworkGroup] | 26.5 | PP network group |
| dRepVotingThresholds[dvtPPEconomicGroup] | 26.6 | PP economic group |
| dRepVotingThresholds[dvtPPTechnicalGroup] | 26.7 | PP technical group |
| dRepVotingThresholds[dvtPPGovGroup] | 26.8 | PP governance group |
| dRepVotingThresholds[dvtTreasuryWithdrawal] | 26.9 | treasury withdrawal |
| committeeMinSize | 27 | min committee size |
| committeeMaxTermLimit | 28 | committee term limit |
| govActionLifetime | 29 | governance action validity lifetime |
| govDeposit | 30 | governance action deposit |
| dRepDeposit | 31 | DRep deposit |
| dRepActivity | 32 | DRep inactivity period |
| minFeeRefScriptCoinsPerByte | 33 | MinFee RefScriptCostPerByte |

## Documentation Traceability

We refer to `defaultConstitution.json` as "the JSON file" in the rest of this document.

Note: Some `$comment`in the JSON file do not match the Interim Constitution. They are ignored by the script and present no incidence on the constitution script.

They will be fixed in a subsequent version.

### Section 2

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| PARAM-01 | No parameter falls under this requirement | :white_check_mark: |
| PARAM-02 | `"18": { "type": "any"}` | :white_check_mark: |

### Section 2.1

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| PARAM-03 | Enforced by [VT-GEN-01] | :white_check_mark: |
| PARAM-05 | Enforced by [VT-GEN-01] | :white_check_mark: |

### Section 2.2

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| TFPB-01 | In "0": `"minValue": 30`| :white_check_mark: |
| TFPB-02 | In "0": `"maxValue": 1000`| :white_check_mark: |
| TFPB-03 | In "0": `"minValue": 0` | :white_check_mark: |

No additional entries in object "0" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| TFF-01 | In "1": `"minValue": 100000` | :white_check_mark: |
| TFF-02 | In "1": `"maxValue": 10000000` | :white_check_mark: |
| TFF-03 | In "1": `"minValue": 0` | :white_check_mark: |

No additional entries in object "1" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| UCPB-01 | In "17": `"minValue": 3000` | :white_check_mark: |
| UCPB-02 | In "17": `"maxValue": 6500`| :white_check_mark: |
| UCPB-03 | In "17": `"notEqual": 0` | :white_check_mark: |
| UCPB-04 | In "17": `"minValue": 0` | :white_check_mark: |

No additional entries in object "17" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| SAD-01 | In "5": `"minValue": 1000000`| :white_check_mark: |
| SAD-02 | In "5": `"maxValue": 5000000` | :white_check_mark: |
| SAD-03 | In "5": `"minValue": 0` | :white_check_mark: |

No additional entries in object "5" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| SPD-01 | In "6": `"minValue": 250000000` | :white_check_mark: |
| SPD-02 | In "6": `"maxValue": 500000000` | :white_check_mark: |
| SPD-03 | In "6": `"minValue": 0` | :white_check_mark: |

No additional entries in object "6" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| MPC-01 | In "16": `minValue": 0`| :white_check_mark: |
| MPC-02 | In "16": `"maxValue": 500000000` | :white_check_mark: |

No additional entries in object "16" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| TC-01 | In "11": `"minValue": { "numerator": 10, "denominator": 100 }` | :white_check_mark: |
| TC-02 | In "11": `"maxValue": { "numerator": 30, "denominator": 100 }` | :white_check_mark: |
| TC-03 | In "11": `"minValue": { "numerator": 0, "denominator": 100 }` | :white_check_mark: |
| TC-04 | In "11": `"maxValue": { "numerator": 100, "denominator": 100 }`| :white_check_mark: |

No additional entries in object "11" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| ME-01 | In "10": `"maxValue": { "numerator": 5, "denominator": 1000 }` | :white_check_mark: |
| ME-02 | In "10": `"minValue": { "numerator": 1, "denominator": 1000 }`| :white_check_mark: |
| ME-03 | In "10": `"minValue": { "numerator": 0, "denominator": 1000 }`| :white_check_mark: |

No additional entries in object "10" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| EIUP-PS-01 | In "19[1]": `"maxValue": { "numerator": 2000, "denominator": 10000000 }` | :white_check_mark: |
| EIUP-PS-02 |  In "19[1]": `"minValue": { "numerator": 500, "denominator": 10000000 }` | :white_check_mark: |

No additional entries in object "19[1]" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| EIUP-PM-01 | In "19[0]": `"maxValue": { "numerator": 2000, "denominator": 10000 }`| :white_check_mark: |
| EIUP-PM-02 | In "19[0]": `"minValue": { "numerator": 400, "denominator": 10000 }` | :white_check_mark: |

No additional entries in object "19[0]" in the JSON file. :white_check_mark

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| MFRS-01 | In "33": `"maxValue": 1000` | :white_check_mark: |
| MFRS-02 | In "33": `"minValue": 0` | :white_check_mark: |

No additional entries in object "33" in the JSON file. :white_check_mark:

### Section 2.3

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| MBBS-01 | In "2": `"maxValue": 122880` | :white_check_mark: |
| MBBS-02 | In "2": `minValue: 24576` | :white_check_mark: |

No additional entries in object "2" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| MTS-01 | In "3": `"maxValue": 32768` | :white_check_mark: |
| MTS-02 | In "3": `"minValue": 0` | :white_check_mark: |

No additional entries in object "3" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| MTEU-M-01 | In "20[0]": `"maxValue": 40000000` | :white_check_mark: |
| MTEU-M-02| In "20[0]": `"minValue": 0` | :white_check_mark: |

No additional entries in object "20[0]" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| MBEU-M-01 | In "21[0]": `"maxValue": 120000000` | :white_check_mark: |
| MBEU-M-02 | In "21[0]": `"minValue": 0` | :white_check_mark: |

No additional entries in object "21[0]" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| MTEU-S-01 | In "20[1]": `"maxValue": 15000000000` | |
| MTEU-S-02 | In "20[1]": `"minValue": 0` | |

No additional entries in object "20[1]" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| MBEU-S-01 | In "21[1]": `"maxValue": 40000000000` | |
| MBEU-S-02 | In "21[1]": `"minValue": 0` | |

No additional entries in object "21[1]" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| MBHS-01 | In "4": `"maxValue": 5000` | :white_check_mark: |
| MBHS-02 | In "4": `"minValue": 0` | :white_check_mark: |


No additional entries in object "4" in the JSON file. :white_check_mark:

### Section 2.4

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| SPTN-01 | In "8": `"minValue": 250` | :white_check_mark: |
| SPTN-02 | In "8": `"maxValue": 2000` | :white_check_mark: |
| SPTN-03 | In "8": `"minValue": 0` | :white_check_mark: |
| SPTN-04 | In "8": `"notEqual": 0` | :white_check_mark: |

No additional entries in object "8" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| PPI-01 | In "9": `"minValue": { "numerator": 1, "denominator": 10 }` | :white_check_mark: |
| PPI-02 | In "9": `"maxValue": { "numerator": 10, "denominator": 10 }` | :white_check_mark: |
| PPI-03 | In "9": `"minValue": { "numerator": 0, "denominator": 10 }` | :white_check_mark: |

No additional entries in object "9" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| PRME-01 | In "7": `"minValue": 0` | :white_check_mark: |

No additional entries in object "7" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| CP-01 | In "23": `"minValue": 100` | :white_check_mark: |
| CP-02 | In "23": `"maxValue": 200` | :white_check_mark: |
| CP-03 | In "23": `"minValue": 0` | :white_check_mark: |
| CP-04 | In "23": `"notEqual": 0` | :white_check_mark: |

No additional entries in object "23" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| MCI-01 | In "24": `"minValue": 1` | :white_check_mark: |

No additional entries in object "24" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| MVS-01 | In "22": `"maxValue": 12288` | :white_check_mark: |
| MVS-02 | In "22": `"minValue": 0` | :white_check_mark: |

No additional entries in object "22" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| Plutus Cost Models | In "18": `"type": "any"` | :white_check_mark: |

No checkable guardrails for Plutus Cost Models. PARAM-02 applies. :white_check_mark:

No additional entries in object "18" in the JSON file. :white_check_mark:

### Section 2.5

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| GD-01 | In "30": `"minValue": 0` | :white_check_mark: |
| GD-02 | In "30": `"minValue": 1000000` | :white_check_mark: |
| GD-03 | In "30": `"maxValue": 10000000000000` | :white_check_mark: |

No additional entries in object "30" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| DRD-01 | In "31": `"minValue": 0` | :white_check_mark: |
| DRD-02 | In "31": `"minValue": 1000000` | :white_check_mark: |
| DRD-03 | In "31": `"maxValue": 100000000000` | :white_check_mark: |

No additional entries in object "31" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| DRA-01 | In "32": `"minValue": 13` | :white_check_mark: |
| DRA-02 | In "32": `"maxValue": 37` | :white_check_mark: |
| DRA-03 | In "32": `"minValue": 0` | :white_check_mark: |

No additional entries in object "32" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| VT-GEN-01 | In "25[0]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "25[1]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "25[2]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "25[3]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "25[4]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "26[0]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "26[1]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "26[2]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "26[3]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "26[4]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "26[5]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "26[6]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "26[7]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "26[8]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> In "26[9]": `"minValue": { "numerator": 50, "denominator": 100 }`, `"maxValue": { "numerator": 100, "denominator": 100 }` <br> | :white_check_mark: |
| VT-GEN-02 | In "26[5]": `"minValue": { "numerator": 51, "denominator": 100 }`, `"maxValue": { "numerator": 75, "denominator": 100 }` <br> In "26[6]": `"minValue": { "numerator": 51, "denominator": 100 }`, `"maxValue": { "numerator": 75, "denominator": 100 }` <br> In "26[7]": `"minValue": { "numerator": 51, "denominator": 100 }`, `"maxValue": { "numerator": 75, "denominator": 100 }` <br> | :white_check_mark: |
| VT-GEN-03 | In "26[8]": `minValue": { "numerator": 75, "denominator": 100 }`, `"maxValue": { "numerator": 90, "denominator": 100 }` | :white_check_mark: |
| VT-HF-01 | In "25[3]": `"minValue": { "numerator": 51, "denominator": 100 }`, `"maxValue": { "numerator": 80, "denominator": 100 }` <br> In "26[4]": `"minValue": { "numerator": 51, "denominator": 100 }`, `"maxValue": { "numerator": 80, "denominator": 100 }` <br> | :white_check_mark: |
| VT-CON-01 | In "26[3]": `"minValue": { "numerator": 65, "denominator": 100 }`, `"maxValue": { "numerator": 90, "denominator": 100 }` | :white_check_mark: |
| VT-CC-01 | In "25[1]": `"minValue": { "numerator": 65, "denominator": 100 }`, `"maxValue": { "numerator": 90, "denominator": 100 }` <br> In "25[2]": `"minValue": { "numerator": 65, "denominator": 100 }`, `"maxValue": { "numerator": 90, "denominator": 100 }` <br> In "26[1]": `"minValue": { "numerator": 65, "denominator": 100 }`, `"maxValue": { "numerator": 90, "denominator": 100 }` <br> In "26[2]": `"minValue": { "numerator": 65, "denominator": 100 }`, `"maxValue": { "numerator": 90, "denominator": 100 }`| :white_check_mark: |
| VT-NC-01 | In "25[0]": `"minValue": { "numerator": 51, "denominator": 100 }`, `"maxValue": { "numerator": 75, "denominator": 100 }` <br> In "26[0]": `"minValue": { "numerator": 51, "denominator": 100 }`, `"maxValue": { "numerator": 75, "denominator": 100 }`| :white_check_mark: |

:question: This is the traceability inferred: 

- 25[0]: VT-GEN-01, VT-NC-01
- 25[1]: VT-GEN-01, VT-CC-01
- 25[2]: VT-GEN-01, VT-CC-01
- 25[3]: VT-GEN-01, VT-HF-01
- 25[4]: VT-GEN-01

- 26[0]: VT-GEN-01, VT-NC-01
- 26[1]: VT-GEN-01, VT-CC-01
- 26[2]: VT-GEN-01, VT-CC-01
- 26[3]: VT-GEN-01, VT-CON-01
- 26[4]: VT-GEN-01, VT-HF-01
- 26[5]: VT-GEN-01, VT-GEN-02
- 26[6]: VT-GEN-01, VT-GEN-02
- 26[7]: VT-GEN-01, VT-GEN-02
- 26[8]: VT-GEN-01, VT-GEN-03
- 26[9]: VT-GEN-01

No additional in objects: "25[0]", "25[1]", "25[2]", "25[3]", "25[4]", "26[0]", "26[1]", "26[2]", "26[3]", "26[4]", "26[5]", "26[6]", "26[7]", "26[8]", and "26[9]" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| GAL-01 | In "29": `"minValue": 1` | :white_check_mark: |
| GAL-02 | In "29": `"maxValue": 15` | :white_check_mark: |

No additional entries in object "29" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| CMTL-01 | In "28": `"notEqual": 0` | :white_check_mark: |
| CMTL-02 | In "28": `"minValue": 0` | :white_check_mark: |
| CMTL-03 | In "28": `"minValue": 18` | :white_check_mark: |
| CMTL-04 | In "28": `"maxValue": 293` | :white_check_mark: |

No additional entries in object "28" in the JSON file. :white_check_mark:

| Interim Constitution Guardrail | Entry in the JSON file | Status |
| --- | --- | -- |
| CMS-01 | In "27": `"minValue": 0` | :white_check_mark: |
| CMS-02 | In "27": `"minValue": 3` | :white_check_mark: |
| CMS-03 | In "27": `"maxValue": 10` | :white_check_mark: |

No additional entries in object "27" in the JSON file. :white_check_mark:

### Section 2.6

BLANK

### Section 2.7

BLANK

### Section 3

BLANK

### Section 4

BLANK

### Section 5

BLANK

### Section 6

BLANK

### Section 7

BLANK

### Section 8

BLANK

## Other entries in the JSON file

There are no additional entries in the JSON file that are not covered by the Interim Constitution. :white_check_mark:
