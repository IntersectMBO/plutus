# Constitution Script Testing Traceability

# Version

Version: 1.1

## Authors 

Bogdan Manole (bogdan.manole@iohk.io)
Romain Soulat (romain.soulat@iohk.io)

## Table of contents

- [Revision History](#revision-history)
- [References](#references)
- [Traceability](#traceability)

## Revision History

| Version | Date | Authors | Comments |
|---|---|---|---|
| 1.0 | April, 30, 2024 | Bogdan Manole, Romain Soulat | Initial version |
| 1.1 | May, 14, 2024 | Romain Soulat | Update to May 07 version of the Constitution |

## References

- [Constitution](https://docs.google.com/document/d/1GwI_6qzfTa5V_BeEY4f-rZNhbfA8lXon)
  - SHA 256: `XX`
  - Date: May, 14, 2024 (latest)

- Testing Framework
  - Old constitution repo Commit: c422981
  - Date: May, 15, 2024 

## Traceability

### Assumptions

The Introduction section of the Constitution states:
*This script is executed whenever a governance action is submitted on-chain. It acts as an additional safeguard to the ledger rule and types, filtering non-compliant governance actions. Guardrails only affect two types of governance actions:*

*1. Protocol Update Actions, and*
*2. Treasury Withdrawal Actions.*

#### Assumption 1

The script will only be called on Protocol Update Actions and Treasury Withdrawal Actions.

#### Assumption 2

The script assumes all the guarantees provided by the ledger rules and types.

### Guardrails and Guidelines on Protocol Update Actions

#### :black_square_button: Critical Protocol Parameters

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
|PARAM-01| :white_check_mark: | No parameters were found to fall into this guardrail  |  :black_square_button: |
|PARAM-02| :white_check_mark: | Cost Models follow PARAM-02  |  :black_square_button: |
|PARAM-03| :white_check_mark: | The script cannot enforce this guardrail directly, it is enforced by [VT-GEN-XX] |  :black_square_button: |
|PARAM-04| :x: | | :white_check_mark: |
|PARAM-05| :white_check_mark: | The script cannot enforce this guardrail directly, it is enforced by [VT-GEN-XX] |  :black_square_button: |
|PARAM-06| :x: | | :white_check_mark: |

#### Economic Parameters

##### Transaction Fee per Byte and fixed transaction fee

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| TFPB-01 | :white_check_mark: | ("TFPB-01", "txFeePerByte must not be lower than 30 (0.000030 ada)")     `MustNotBe` NL    30 | :white_check_mark: |
| TFPB-02 | :white_check_mark: | ("TFPB-02", "txFeePerByte must not exceed 1,000 (0.001 ada)")  `MustNotBe` NG 1_000 | :white_check_mark: |
| TFPB-03 | :white_check_mark: | ("TFPB-03", "txFeePerByte must not be negative")               `MustNotBe` NL     0 | :white_check_mark: |
| TFF-01 | :white_check_mark: | ("TFF-01","txFeeFixed must not be lower than 100,000 (0.1 ada)")   `MustNotBe` NL 100_000 | :white_check_mark: |
| TFF-02 | :white_check_mark: | ("TFF-02","txFeeFixed must not exceed 10,000,000 (10 ada)")          `MustNotBe` NG 10_000_000 | :white_check_mark: |
| TFF-03 | :white_check_mark: | ("TFF-03","txFeeFixed must not be negative")                            `MustNotBe` NL     0 | :white_check_mark: |
| TFGEN-01 | :x: | | :white_check_mark: |
| TFGEN-02 | :x: | | :white_check_mark: |

##### UTxO cost per byte

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| UCPB-01 | :white_check_mark: | ("UCPB-01","utxoCostPerByte must not be lower than 3,000 (0.003 ada)")   `MustNotBe` NL 3_000 | :white_check_mark: |
| UCPB-02 | :white_check_mark: | ("UCPB-02","utxoCostPerByte must not exceed 6,500 (0.0065 ada)") `MustNotBe` NG 6_500 | :white_check_mark: |
| UCPB-03 | :white_check_mark: | Once (("UCPB-03","utxoCostPerByte must not be zero")              `MustNotBe` NEQ     0) | :white_check_mark: |
| UCPB-04 | :white_check_mark: | ("UCPB-04","utxoCostPerByte must not be negative")             `MustNotBe` NL      0 | :white_check_mark: |
| UCPB-05 | :x: | | :white_check_mark: |

##### Stake address deposit

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| SAD-01 | :white_check_mark: | ("SAD-01","stakeAddressDeposit must not be lower than 1,000,000 (1 ada)") `MustNotBe` NL 1_000_000 | :white_check_mark: |
| SAD-02 | :white_check_mark: | ("SAD-02","stakeAddressDeposit must not exceed 5,000,000 (5 ada)") `MustNotBe` NG 5_000_000 | :white_check_mark: |
| SAD-03 | :white_check_mark: | ("SAD-03","stakeAddressDeposit must not be negative")                        `MustNotBe` NL 0 | :white_check_mark: |

##### Stake pool deposit

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| SPD-01 | :white_check_mark: | ("SPD-01","stakePoolDeposit must not be lower than 250,000,000 (250 ada)") `MustNotBe` NL 250_000_000 | :white_check_mark: |
| SPD-02 | :white_check_mark: | ("SPD-02","stakePoolDeposit must not exceed 500,000,000 (500 ada)") `MustNotBe` NG 500_000_000 | :white_check_mark: |
| SPD-03 | :white_check_mark: | ("SDP-03","stakePoolDeposit must not be negative")                            `MustNotBe` NL 0 | :white_check_mark: |

##### Minimum pool cost

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| MPC-01 | :white_check_mark: | ("MPC-01","minPoolCost must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| MPC-02 | :white_check_mark: | ("MPC-02","minPoolCost must not exceed 500,000,000 (500 ada)") `MustNotBe` NG 500_000_000 | :white_check_mark: |
| MPC-03 | :x: | | :white_check_mark: |

##### Treasury Cut

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| TC-01 | :white_check_mark: | ("TC-01","treasuryCut must not be lower than 0.1 (10%)") `MustNotBe` NL 0.1 | :white_check_mark: |
| TC-02 | :white_check_mark: | ("TC-02", "treasuryCut must not exceed 0.3 (30%)") `MustNotBe` NG 0.3 | :white_check_mark: |
| TC-03 | :white_check_mark: | ("TC-03","treasuryCut must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| TC-04 | :white_check_mark: | ("TC-04", "treasuryCut must not exceed 1.0 (100%)") `MustNotBe` NG 1.0 | :white_check_mark: |
| TC-05 | :x: | | :white_check_mark: |

##### Monetary Expansion Rate

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| ME-01 | :white_check_mark: | ("ME-01","monetaryExpansion must not exceed 0.005") `MustNotBe` NG 0.005 | :white_check_mark: |
| ME-02 | :white_check_mark: | ("ME-02","monetaryExpansion must not be lower than 0.001") `MustNotBe` NL 0.001 | :white_check_mark: |
| ME-03 | :white_check_mark: | ("ME-03","monetaryExpansion must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| ME-04 | :x: | | :white_check_mark: |
| ME-05 | :x: | | :white_check_mark: |

##### Plutus Script Execution Prices

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| EIUP-PS-01 | :white_check_mark: | ("EIUP-PS-01","executionUnitPrices[priceSteps] must not exceed 2,000 / 10,000,000") `MustNotBe` NG (2_000 % 10_000_000) | :white_check_mark: |
| EIUP-PS-02 | :white_check_mark: | ("EIUP-PS-02","executionUnitPrices[priceSteps] must not be lower than 500 / 10,000,000") `MustNotBe` NL (500 % 10_000_000) | :white_check_mark: |
| EIUP-PM-01 | :white_check_mark: | ("EIUP-PM-01","executionUnitPrices[priceMemory] must not exceed 2_000 / 10_000") `MustNotBe` NG (2_000 % 10_000) | :white_check_mark: |
| EIUP-PM-02 | :white_check_mark: | ("EIUP-PM-02","executionUnitPrices[priceMemory] must not be lower than 400 / 10_000") `MustNotBe` NL (400 % 10_000) | :white_check_mark: |
| EIUP-GEN-01 | :x: | | :white_check_mark: |
| EIUP-GEN-02 | :x: | | :white_check_mark: |

##### Transaction fee per byte for a reference script

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| MFRS-01 | :white_check_mark: | ("MFRS-01", "minFeeRefScriptCoinsPerByte must not exceed 1,000 (0.001 ada)") `MustNotBe` NG 1_000 | :white_check_mark: |
| MFRS-02 | :white_check_mark: | ("MFRS-02", "minFeeRefScriptCoinsPerByte must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| MFRS-03 | :x: | | :white_check_mark: |
| MFRS-04 | :x: | | :white_check_mark: |

#### Network Parameters

| Guardrail ID | Checkable | Checked by (if applicable) | Validation |
|---|:---:|---|:---:|
| NETWORK-1 | :x: | | :white_check_mark: |
| NETWORK-2 | :x: | | :white_check_mark: |

##### Block Size

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| MBBS-01 | :white_check_mark: | ("MBBS-01","maxBlockBodySize must not exceed 122,880 Bytes (120KB)")         `MustNotBe` NG 122_880 | :white_check_mark: |
| MBBS-02 | :white_check_mark: | ("MBBS-02","maxBlockBodySize must not be lower than 24,576 Bytes (24KB)") `MustNotBe` NL 24_576 | :white_check_mark: |
| MBBS-03 | :x: | | :white_check_mark: |
| MBBS-04 | :x: | | :white_check_mark: |
| MBBS-05 | :x: | | :white_check_mark: |
| MBBS-06 | :x: | | :white_check_mark: |

##### Transaction size

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| MTS-01 | :white_check_mark: | ("MTS-01","maxTxSize must not exceed 32,768 Bytes (32KB)")                  `MustNotBe` NG 32_768 | :white_check_mark: |
| MTS-02 | :white_check_mark: | ("MTS-02","maxTxSize must not be negative")                                 `MustNotBe` NL     0 | :white_check_mark: |
| MTS-03 | :x: | | :white_check_mark: |
| MTS-04 | :x: | | :white_check_mark: |
| MTS-05 | :x: | | :white_check_mark: |
| MTS-06 | :x: | | :white_check_mark: |

##### Memory Unit Limites

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| MTEU-M-01 | :white_check_mark: | ("MTEU-M-01","maxTxExecutionUnits[memory] must not exceed 40,000,000 units") `MustNotBe` NG 40_000_000 | :white_check_mark: |
| MTEU-M-02 | :white_check_mark: | ("MTEU-M-02","maxTxExecutionUnits[memory] must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| MTEU-M-03 | :x: | | :white_check_mark: |
| MTEU-M-04 | :x: | | :white_check_mark: |
| MBEU-M-01 | :white_check_mark: | ("MBEU-M-01","maxBlockExecutionUnits[memory] must not exceed 120,000,000 units") `MustNotBe` NG 120_000_000 | :white_check_mark: |
| MBEU-M-02 | :white_check_mark: | ("MBEU-M-02","maxBlockExecutionUnits[memory] must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| MBEU-M-03 | :x: | | :white_check_mark: |
| MBEU-M-04 | :x: | | :white_check_mark: |
| MTEU-GEN-01 | :x: | | :white_check_mark: |

##### CPU Unit Limits

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| MTEU-S-01 | :white_check_mark: | ("MTEU-S-01","maxTxExecutionUnits[steps] must not exceed 15,000,000,000 (15Bn) units") `MustNotBe` NG 15_000_000_000 | :white_check_mark: |
| MTEU-S-02 | :white_check_mark: | ("MTEU-S-02","maxTxExecutionUnits[steps] must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| MTEU-S-03 | :x: | | :white_check_mark: |
| MBEU-S-01 | :white_check_mark: | ("MBEU-S-01","maxBlockExecutionUnits[steps] must not exceed 40,000,000,000 (40Bn) units") `MustNotBe` NG 40_000_000_000 | :white_check_mark: |
| MBEU-S-02 | :white_check_mark: | ("MBEU-S-02","maxBlockExecutionUnits[steps] must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| MTEU-S-04 | :x: | | :white_check_mark: |
| MBEU-S-03 | :x: | | :white_check_mark: |
| MEU-S-01 | :x: | | :white_check_mark: |

##### Block Header Size

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| MBHS-01 | :white_check_mark: | ("MBHS-01","maxBlockHeaderSize must not exceed 5,000 Bytes")                `MustNotBe` NG 5_000 | :white_check_mark: |
| MBHS-02 | :white_check_mark: | ("MBHS-02","maxBlockHeaderSize must not be negative")                       `MustNotBe` NL     0 | :white_check_mark: |
| MBHS-03 | :x: | | :white_check_mark: |
| MBHS-04 | :x: | | :white_check_mark: |
| MBHS-05 | :x: | | :white_check_mark: |

#### Technical/Security Parameters

##### Target Number of Stake Pools

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| SPTN-01 | :white_check_mark: | ("SPTN-01","stakePoolTargetNum must not be lower than 250") `MustNotBe` NL 250 | :white_check_mark: |
| SPTN-02 | :white_check_mark: | ("SPTN-02","stakePoolTargetNum must not exceed 2,000") `MustNotBe` NG 2_000 | :white_check_mark: |
| SPTN-03 | :white_check_mark: | ("SPTN-03","stakePoolTargetNum must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| SPTN-04 | :white_check_mark: | ("SPTN-04", "stakePoolTargetNum must not be zero") `MustNotBe` NEQ 0 | :white_check_mark: |

##### Pledge Influence Factor

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| PPI-01 | :white_check_mark: | ("PPI-01","poolPledgeInfluence must not be lower than 0.1") `MustNotBe` NL (1 % 10) | :white_check_mark: |
| PPI-02 | :white_check_mark: | ("PPI-02","poolPledgeInfluence must not exceed 1.0") `MustNotBe` NG (10 % 10) | :white_check_mark: |
| PPI-03 | :white_check_mark: | ("PPI-03","poolPledgeInfluence must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| PPI-04 | :x: | | :white_check_mark: |

##### Pool Retirement Window

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| PRME-01 | :white_check_mark: | ("PRME-01","poolRetireMaxEpoch must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| PRME-02 | :x: | | :white_check_mark: |

##### Collateral Percentage

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| CP-01 | :white_check_mark: | ("CP-01","collateralPercentage must not be lower than 100") `MustNotBe` NL 100 | :white_check_mark: |
| CP-02 | :white_check_mark: | ("CP-02","collateralPercentage must not exceed 200") `MustNotBe` NG 200 | :white_check_mark: |
| CP-03 | :white_check_mark: | ("CP-03","collateralPercentage must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| CP-04 | :white_check_mark: | ("CP-04","collateralPercentage must not be zero") `MustNotBe` NEQ 0 | :white_check_mark: |

##### Maximum number of collateral inputs

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| MCI-01 | :white_check_mark: | ("MCI-01","maxCollateralInputs must not be lower than 1") `MustNotBe` NL 1 | :white_check_mark: |

##### Maximum Value Size

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| MVS-01 | :white_check_mark: | ("MVS-01","maxValueSize must not exceed 12,288 Bytes (12KB)") `MustNotBe` NG 12_288 | :white_check_mark: |
| MVS-02 | :white_check_mark: | ("MVS-02","maxValueSize must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| MVS-03 | :x: | | :white_check_mark: |
| MVS-04 | :x: | | :white_check_mark: |
| MVS-05 | :x: | | :white_check_mark: |

##### :x: Plutus Cost Models

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| PCM-01 | :x: | | :white_check_mark: |
| PCM-02 | :x: | | :white_check_mark: |
| PCM-03 | :x: | | :white_check_mark: |
| PCM-04 | :x: | | :white_check_mark: |

Note: Test cases exist for the Plutus Cost Models, the presence of a Cost model will not change the output of the script.

#### Governance Parameters

##### Deposit for Governance Actions

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| GD-01 | :white_check_mark: | ("GD-01", "govDeposit must not be negative" ) `MustNotBe` NL 0 | :white_check_mark: |
| GD-02 | :white_check_mark: | ("GD-02", "govDeposit must not be lower than 1,000,000 (1 ada)") `MustNotBe` NL 1_000_000 | :white_check_mark: |
| GD-03 | :white_check_mark: | ("GD-03", "govDeposit must not be more than 10,000,000,000,000 (10 Million ada)") `MustNotBe` NG 10_000_000_000_000 | :white_check_mark: |
| GD-04 | :x: | | :white_check_mark: |

##### Deposit for DReps

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| DRD-01 | :white_check_mark: | ("DRD-01", "dRepDeposit must not be negative" ) `MustNotBe` NL 0 | :white_check_mark: |
| DRD-02 | :white_check_mark: | ("DRD-02", "dRepDeposit must not be lower than 1,000,000 (1 ada)") `MustNotBe` NL 1_000_000 | :white_check_mark: |
| DRD-03 | :white_check_mark: | ("DRD-03", "dRepDeposit must be no more than 100,000,000,000 (100,000 ada)") `MustNotBe` NG 100_000_000_000 | :white_check_mark: |
| DRD-04 | :x: | | :white_check_mark: |

##### Deposit Activity Period

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| DRA-01 | :white_check_mark: | ("DRA-01", "dRepActivity must not be less than 13 epochs (2 months)") `MustNotBe` NL 13 | :white_check_mark: |
| DRA-02 | :white_check_mark: | ("DRA-02", "dRepActivity must not exceed 37 epochs (6 months)") `MustNotBe` NG 37 | :white_check_mark: |
| DRA-03 | :white_check_mark: | ("DRA-03", "dRepActivity must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| DRA-04 | :x: | | :white_check_mark: |
| DRA-05 | :x: | | :white_check_mark: |

##### Drep and SPO Governance Action Thresholds

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| VT-GEN-01 | :white_check_mark: | **poolVotingThresholds = ParamList @Rational 25 "poolVotingThresholds"**  <br> Param 0 "motionNoConfidence" (2 % 3) <br> ("VT-GEN-01" ,"All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 1 "committeeNormal" (2 % 3) <br> ("VT-GEN-01" ,"All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 2 "committeeNoConfidence" (2 % 3) <br>("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br>("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 3 "hardForkInitiation" (2 % 3)<br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 4 "ppSecurityGroup" (2 % 3) <br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> **dRepVotingThresholds = Collection @Rational 26 "dRepVotingThresholds"**  <br>Param 0 "motionNoConfidence" (2 % 3) <br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 1 "committeeNormal" (2 % 3) <br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1)  <br><br>Param 2 "committeeNoConfidence" (2 % 3) <br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 3 "updateConstitution" (2 % 3) <br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 4 "hardForkInitiation" (2 % 3) <br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 5 "ppNetworkGroup" (2 % 3) <br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 6 "ppEconomicGroup" (2 % 3) <br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 7 "ppTechnicalGroup" (2 % 3) <br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 8 "ppGovernanceGroup" (2 % 3) <br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> Param 9 "treasuryWithdrawal" (2 % 3) <br> ("VT-GEN-01","All thresholds must be in the range 50%-100%") `MustNotBe` NL (1 % 2) <br> ("VT-GEN-01b","All thresholds must be in the range 50%-100%") `MustNotBe` NG (1 % 1) <br><br> | :white_check_mark: |
| VT-GEN-02 | :white_check_mark: | **dRepVotingThresholds = Collection @Rational 26 "dRepVotingThresholds"** <br> Param 5 "ppNetworkGroup" (2 % 3) <br>("VT-GEN-02", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NL (51 % 100) <br> ("VT-GEN-02b", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NG (75 % 100) <br><br> Param 6 "ppEconomicGroup" (2 % 3) <br>("VT-GEN-02", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NL (51 % 100) <br> ("VT-GEN-02b", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NG (75 % 100) <br><br> Param 7 "ppTechnicalGroup" (2 % 3) <br>("VT-GEN-02", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NL (51 % 100) <br> ("VT-GEN-02b", "Economic, network, and technical parameters thresholds must be in the range 51%-75%") `MustNotBe` NG (75 % 100)  | :white_check_mark: |
| VT-GOV-01 | :white_check_mark: | **dRepVotingThresholds = ParamList @Rational 26 "dRepVotingThresholds"** <br>Param 8 "ppGovernanceGroup" (4 % 5) <br> ("VT-GOV-01", "Governance parameter thresholds must be in the range 75%-90%") `MustNotBe` NL (75 % 100) <br> ("VT-GOV-01b", "Governance parameter thresholds must be in the range 75%-90%") `MustNotBe` NG (90 % 100) | :white_check_mark: |
| VT-HF-01 | :white_check_mark: | **poolVotingThresholds = ParamList @Rational 25 "poolVotingThresholds"**<br> Param 3 "hardForkInitiation" (2 % 3) <br> ("VT-HF-01", "Hard fork action thresholds must be in the range 51%-80%") `MustNotBe` NL (51 % 100) <br> ("VT-HF-01b", "Hard fork action thresholds must be in the range 51%-80%") `MustNotBe` NG (80 % 100) <br><br> **dRepVotingThresholds = ParamList @Rational 26 "dRepVotingThresholds"** <br> Param 4 "hardForkInitiation" (2 % 3) <br> ("VT-HF-01", "Hard fork action thresholds must be in the range 51%-80%") `MustNotBe` NL (51 % 100) <br> ("VT-HF-01b", "Hard fork action thresholds must be in the range 51%-80%") `MustNotBe` NG (80 % 100)| :white_check_mark: |
| VT-CON-01 | :white_check_mark: | **dRepVotingThresholds = ParamList @Rational 26 "dRepVotingThresholds"** <br> Param 3 "updateConstitution" (2 % 3) <br> ("VT-CON-01", "Update Constitution or proposal policy action thresholds must be in the range 65%-90%") `MustNotBe` NL (65 % 100) <br> ("VT-CON-01b", "Update Constitution or proposal policy action thresholds must be in the range 65%-90%") `MustNotBe` NG (90 % 100)  | :white_check_mark: |
| VT-CC-01 | :white_check_mark: | **poolVotingThresholds = ParamList @Rational 25 "poolVotingThresholds"** <br> Param 1 "committeeNormal" (2 % 3) <br> ("VT-CC-01","Update Constitutional Committee action thresholds must be in the range 65%-90%") `MustNotBe` NL (65 % 100) <br> ("VT-CC-01b","Update Constitutional Committee action thresholds must be in the range 65%-90%") `MustNotBe` NG (90 % 100) <br><br> Param 2 "committeeNoConfidence" (2 % 3) <br> ("VT-CC-01","Update Constitutional Committee action thresholds must be in the range 65%-90%") `MustNotBe` NL (65 % 100) <br> ("VT-CC-01b","Update Constitutional Committee action thresholds must be in the range 65%-90%") `MustNotBe` NG (90 % 100) <br><br>  **dRepVotingThresholds = ParamList @Rational 26 "dRepVotingThresholds"** <br> Param 1 "committeeNormal" (2 % 3) <br> ("VT-CC-01","Update Constitutional Committee action thresholds must be in the range 65%-90%") `MustNotBe` NL (65 % 100) <br> ("VT-CC-01b","Update Constitutional Committee action thresholds must be in the range 65%-90%") `MustNotBe` NG (90 % 100) <br><br> Param 2 "committeeNoConfidence" (2 % 3) <br> ("VT-CC-01","Update Constitutional Committee action thresholds must be in the range 65%-90%") `MustNotBe` NL (65 % 100) <br> ("VT-CC-01b","Update Constitutional Committee action thresholds must be in the range 65%-90%") `MustNotBe` NG (90 % 100)| :white_check_mark: |
| VT-NC-01 | :white_check_mark: | **poolVotingThresholds = ParamList @Rational 25 "poolVotingThresholds"** <br>Param 0 "motionNoConfidence" (2 % 3) <br> ("VT-NC-01", "No confidence action thresholds must be in the range 51%-75%") `MustNotBe` NL (51 % 100) <br>  ("VT-NC-01b", "No confidence action thresholds must be in the range 51%-75%") `MustNotBe` NG (75 % 100) <br><br> **dRepVotingThresholds = ParamList @Rational 26 "dRepVotingThresholds"** <br>Param 0 "motionNoConfidence" (2 % 3) <br> ("VT-NC-01", "No confidence action thresholds must be in the range 51%-75%") `MustNotBe` NL (51 % 100) <br>  ("VT-NC-01b", "No confidence action thresholds must be in the range 51%-75%") `MustNotBe` NG (75 % 100)  | :white_check_mark: |

##### Governance Action Lifetime

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| GAL-01 | :white_check_mark: | ("GAL-01", "govActionLifetime must not be less than 1 epoch (5 days)") `MustNotBe` NL 1 | :white_check_mark: |
| GAL-03 | :x: | | :white_check_mark: |
| GAL-02 | :white_check_mark: | ("GAL-02", "govActionLifetime must not be greater than 15 epochs (75 days)") `MustNotBe` NG 15 | :white_check_mark: |
| GAL-04 | :x: | | :white_check_mark: |
| GAL-05 | :x: | | :white_check_mark: |

##### Maximum Constitutional Committee Term

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| CMTL-01 | :white_check_mark: | ("CMTL-01", "committeeMaxTermLimit must not be zero") `MustNotBe` NEQ 0 | :white_check_mark: |
| CMTL-02 | :white_check_mark: | ("CMTL-01b", "committeeMaxTermLimit must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| CMTL-03 | :white_check_mark: | ("CMTL-03", "committeeMaxTermLimit must not be less than 18 epochs (90 days, or approximately 3 months)") `MustNotBe` NL 18 | :white_check_mark: |
| CMTL-04 | :white_check_mark: | ("CMTL-03", "committeeMaxTermLimit must not be more than 293 epochs (approximately 4 years)") `MustNotBe` NG 293 | :white_check_mark: |
| CMTL-05 | :x: | | :white_check_mark: |

##### The minimum size of the Constitutional Committee

|Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| CMS-01 | :white_check_mark: | ("CMS-01", "committeeMinSize must not be negative") `MustNotBe` NL 0 | :white_check_mark: |
| CMS-02 | :white_check_mark: | ("CMS-02", "committeeMinSize must not be less than 3") `MustNotBe` NL 3 | :white_check_mark: |
| CMS-03 | :white_check_mark: | ("CMS-03", "committeeMinSize must not be more than 10") `MustNotBe` NG 10 | :white_check_mark: |

#### Monitoring and Reversion of Parameter Changes

BLANK SECTION

#### Non-updatable Protocol Parameters

BLANK SECTION


### :x: Guardrails and Guidelines on Treasury Withdrawal Actions

| Guardrail ID | Checkable | Checked by (if applicable)|Validation |
|---|:---:|---|:---:|
| TREASURY-01 | :x: | | :white_check_mark: |
| TREASURY-02 | :x: | | :white_check_mark: |
| TREASURY-03 | :x: | | :white_check_mark: |
| TREASURY-04 | :x: | | :white_check_mark: |

**Note: The script currently does not validate on this Governance action** :x: 

### Guardrails and Guidelines on Hard Fork Actions

The script is not called on hard fork actions. See [Assumption 1](#assumptions).

### Guardrails and Guidelines on Update Constitutional Committee Actions or Thresholds Actions

The script is not called Update Constitutional Committee Actions or Thresholds Actions. See [Assumption 1](#assumptions).

### Guardrails and Guidelines on Update to the Constitution or Proposal Policy Actions

The script is not called on Update to the Constitution or Proposal Policy Actions. See [Assumption 1](#assumptions).

### Guardrail and Guidelines on No Confidence Actions

The script is not called on No Confidence Actions. See [Assumption 1](#assumptions).

### Guardrail and Guidelines on Info Actions

The script is not called on Info Actions. See [Assumption 1](#assumptions).

### Guardrails during the Interim Period

The script is not called during the Interim Period. See [Assumption 1](#assumptions).
