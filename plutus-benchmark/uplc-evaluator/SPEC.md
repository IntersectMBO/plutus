# UPLC Benchmarking Interface Specification

## Overview

This document specifies the asynchronous SSH/file-based interface for submitting UPLC programs to the dedicated benchmarking environment and retrieving execution metrics.

## Directory Structure

The benchmarking interface uses two primary directories:

### Input Directory
```
/benchmarking/input/
```
This directory is where clients submit UPLC programs and configuration files for evaluation.

**Permissions:** Read/write access for authenticated clients

### Output Directory
```
/benchmarking/output/
```
This directory is where the evaluation service writes results and error files.

**Permissions:** Read-only access for clients, write access for evaluation service

## File Naming Conventions

All files use a consistent naming pattern based on a unique job identifier.

### Job ID Format

The `job_id` is a **UUID v4** (Universally Unique Identifier) that uniquely identifies each evaluation request.

**Format:** 8-4-4-4-12 hexadecimal characters (e.g., `550e8400-e29b-41d4-a716-446655440000`)

**Generation:** Clients must generate a unique UUID for each job submission.

### Program Files

#### Textual UPLC Programs
```
{job_id}.uplc.txt
```
**Example:** `/benchmarking/input/550e8400-e29b-41d4-a716-446655440000.uplc.txt`

Contains UPLC program in textual format following the grammar specified in plutus-core-spec.pdf.

#### Flat-Encoded UPLC Programs
```
{job_id}.uplc.flat
```
**Example:** `/benchmarking/input/550e8400-e29b-41d4-a716-446655440000.uplc.flat`

Contains UPLC program in flat-encoded (CBOR) binary format, the canonical on-chain representation.

### Configuration Files

```
{job_id}.config.json
```
**Example:** `/benchmarking/input/550e8400-e29b-41d4-a716-446655440000.config.json`

Optional configuration file specifying version parameters for evaluation. If omitted, default values are used.

### Result Files

#### Success Results
```
{job_id}.result.json
```
**Example:** `/benchmarking/output/550e8400-e29b-41d4-a716-446655440000.result.json`

Contains successful evaluation results with measurement samples.

#### Error Results
```
{job_id}.error.json
```
**Example:** `/benchmarking/output/550e8400-e29b-41d4-a716-446655440000.error.json`

Contains error information when evaluation fails.

## Complete File Path Examples

### Successful Evaluation Workflow

1. Client submits textual program:
   ```
   /benchmarking/input/a1b2c3d4-e5f6-4789-a012-3456789abcde.uplc.txt
   ```

2. Client optionally submits configuration:
   ```
   /benchmarking/input/a1b2c3d4-e5f6-4789-a012-3456789abcde.config.json
   ```

3. Service writes successful result:
   ```
   /benchmarking/output/a1b2c3d4-e5f6-4789-a012-3456789abcde.result.json
   ```

### Failed Evaluation Workflow

1. Client submits flat-encoded program:
   ```
   /benchmarking/input/f7e8d9c0-b1a2-4567-8901-234567890abc.uplc.flat
   ```

2. Service detects validation error and writes:
   ```
   /benchmarking/output/f7e8d9c0-b1a2-4567-8901-234567890abc.error.json
   ```

## Job Identifier Requirements

- **Format:** UUID v4 (RFC 4122 compliant)
- **Uniqueness:** Each job submission must use a unique UUID
- **Case:** Lowercase hexadecimal characters recommended
- **Validation:** Service validates UUID format before processing

**Example valid job IDs:**
```
550e8400-e29b-41d4-a716-446655440000
a1b2c3d4-e5f6-4789-a012-3456789abcde
f7e8d9c0-b1a2-4567-8901-234567890abc
```

**Example invalid job IDs:**
```
job-123                  # Not UUID format
550e8400e29b41d4         # Missing hyphens
550E8400-E29B-41D4-...   # Uppercase not recommended
not-a-uuid               # Invalid format
```

## Summary Table

| File Type | Extension | Directory | Purpose |
|-----------|-----------|-----------|---------|
| Textual program | `.uplc.txt` | input/ | UPLC program in textual syntax |
| Flat-encoded program | `.uplc.flat` | input/ | UPLC program in binary CBOR format |
| Configuration | `.config.json` | input/ | Optional version parameters |
| Success result | `.result.json` | output/ | Evaluation metrics |
| Error result | `.error.json` | output/ | Error information |

All files follow the naming pattern: `{job_id}.{extension}`

## Textual UPLC Input Format

### File Extension

Textual UPLC programs must use the `.uplc.txt` file extension.

### Grammar Reference

The textual syntax for Untyped Plutus Core follows the grammar specified in **plutus-core-spec.pdf** (see `doc/plutus-core-spec/plutus-core-specification.tex` in the Plutus repository).

### Program Structure

All UPLC programs must follow this top-level structure:
```
(program <version> <term>)
```

Where:
- `<version>` is the language version (e.g., `1.0.0` or `1.1.0`)
- `<term>` is a fully applied UPLC term that evaluates to a value

### Validation Rules

Programs submitted for evaluation must satisfy the following requirements:

1. **Fully Applied**: Programs must be closed terms that evaluate to a value (constant, builtin result, constructor, etc.)
2. **No Free Variables**: All variables must be bound by lambda abstractions
3. **No Unapplied Lambdas**: The program cannot evaluate to a lambda abstraction or delay
4. **No Type Abstractions**: UPLC is untyped; type-level abstractions are not supported

### Valid Program Examples

#### Example 1: Simple Constant
```
(program 1.0.0 (con integer 42))
```
**Evaluates to:** Integer constant `42`

#### Example 2: Arithmetic with Builtins
```
(program 1.0.0
  [ [ (builtin addInteger) (con integer 10) ] (con integer 32) ]
)
```
**Evaluates to:** Integer constant `42` (10 + 32)

#### Example 3: Lambda Application
```
(program 1.0.0
  [ (lam x [ [ (builtin multiplyInteger) x ] (con integer 2) ])
    (con integer 21) ]
)
```
**Evaluates to:** Integer constant `42` (21 × 2)

#### Example 4: Constructor
```
(program 1.1.0
  (constr 0 (con integer 42) (con bool True))
)
```
**Evaluates to:** Constructor with tag `0` and two fields

### Invalid Program Examples

#### Example 1: Unapplied Lambda (INVALID)
```
(program 1.0.0 (lam x x))
```
**Error:** Program evaluates to a lambda abstraction, not a value
**Error Type:** `validation_error`

#### Example 2: Free Variable (INVALID)
```
(program 1.0.0 x)
```
**Error:** Variable `x` is not bound
**Error Type:** `syntax_error`

#### Example 3: Unapplied Builtin (INVALID)
```
(program 1.0.0 (builtin addInteger))
```
**Error:** Builtin `addInteger` requires 2 arguments but received 0
**Error Type:** `validation_error`

### Syntax Elements

Common UPLC syntax elements include:

- **Constants:** `(con <type> <value>)`
  Types: `integer`, `bytestring`, `string`, `unit`, `bool`, `data`, `list`, `pair`

- **Lambda Abstraction:** `(lam <var> <body>)`

- **Application:** `[ <function> <argument> ]`

- **Builtin Functions:** `(builtin <name>)`
  Examples: `addInteger`, `subtractInteger`, `lessThanInteger`, `appendByteString`, etc.

- **Delay/Force:** `(delay <term>)` and `(force <term>)` for lazy evaluation

- **Constructor:** `(constr <tag> <arg1> ... <argN>)` (version 1.1.0+)

- **Case:** `(case <scrutinee> <case1> ... <caseN>)` (version 1.1.0+)

### Comments

Programs may include comments using `--` for single-line comments:
```
-- This is a comment
(program 1.0.0 (con integer 42))
```

## Flat-Encoded UPLC Input Format

### File Extension

Flat-encoded UPLC programs must use the `.uplc.flat` file extension.

### Format Reference

The flat encoding format for Untyped Plutus Core follows the specification in **plutus-core-spec.pdf** (see `doc/plutus-core-spec/plutus-core-specification.tex`, Appendix: "Serialising Plutus Core Terms and Programs Using the flat Format").

### Canonical On-Chain Format

**Important:** The flat encoding is the **canonical on-chain format** used by the Cardano blockchain. It is the definitive concrete representation of Plutus Core programs.

- All scripts deployed on Cardano are stored in flat-encoded format (wrapped in CBOR for consistency with other chain objects)
- Flat encoding is a bit-oriented format optimized for minimal size
- Benchmarks show flat encoding produces serialized scripts approximately **35% smaller** than CBOR encoding
- Flat-encoded programs use de Bruijn indices for variable representation, further reducing size

### Format Characteristics

The flat encoding:
- Uses bit-level encoding (not byte-aligned until padding)
- Employs variable-length integer encoding
- Represents terms using 4-bit tags
- Encodes types using 4-bit tags
- Uses 7-bit tags for builtin functions
- Adds padding to ensure final output is byte-aligned

### Example Conversion

The `uplc` executable can convert between textual and flat-encoded formats:

```bash
# Convert textual to flat
uplc convert --from textual --to flat -i program.uplc.txt -o program.uplc.flat

# Convert flat to textual (for verification)
uplc convert --from flat --to textual -i program.uplc.flat -o program.uplc.txt
```

### Validation

Flat-encoded programs submitted for evaluation must satisfy the same validation rules as textual programs:
1. **Fully Applied**: Programs must evaluate to values
2. **No Free Variables**: All variables must be bound
3. **No Unapplied Lambdas**: Cannot evaluate to lambda/delay
4. **Well-Scoped**: De Bruijn indices must be valid (automatically checked during deserialization)

### Binary Format Details

For detailed information on the binary encoding scheme, including:
- Version number encoding
- Term tag assignments (0-9)
- Type tag assignments
- Builtin function tags
- Padding and alignment rules
- De Bruijn index encoding

Refer to **plutus-core-spec.pdf**, Appendix on flat serialisation.

## Configuration File Format

### File Extension

Configuration files use the `.config.json` file extension and follow the job ID naming convention: `{job_id}.config.json`

### Format

Configuration files are JSON objects that specify version parameters for UPLC program evaluation. These parameters control which protocol version, ledger language, UPLC version, and cost model are used during evaluation.

### Configuration Scope

Configuration can be specified at two levels:

1. **Per-Job Configuration**: Submit `{job_id}.config.json` alongside each program file for job-specific parameters
2. **Global Default Configuration**: Maintained by the service administrator for all jobs that don't specify custom configuration

**Recommendation**: Use per-job configuration when testing against specific protocol versions or cost models. Rely on global defaults for typical mainnet evaluation.

### Configuration Schema

```json
{
  "protocol_version": <integer>,
  "ledger_language": <string>,
  "uplc_version": <string>,
  "cost_model_params": <object | null>
}
```

### Fields

#### `protocol_version` (required)

The Cardano protocol version number (major version). This determines which features and builtins are available.

**Type**: Integer

**Valid values**:
- `5` - Alonzo (PlutusV1 introduction)
- `7` - Vasil (PlutusV2 introduction)
- `8` - Valentine
- `9` - Chang (PlutusV3 introduction)
- `10` - Plomin (latest mainnet as of 2026-01)
- `11` - Future protocol version (pre-release)

**Example**: `10`

#### `ledger_language` (required)

The Plutus ledger language version used for evaluation. This determines the set of available builtins and evaluation semantics.

**Type**: String

**Valid values**:
- `"PlutusV1"` - Original Plutus (available from protocol v5+)
- `"PlutusV2"` - Enhanced Plutus with additional builtins (available from protocol v7+)
- `"PlutusV3"` - Latest Plutus with BLS12-381 and bitwise operations (available from protocol v9+)

**Example**: `"PlutusV3"`

**Note**: Ledger language must be available in the specified protocol version. For example, `PlutusV3` requires protocol version ≥ 9.

#### `uplc_version` (required)

The Untyped Plutus Core language version. This determines which UPLC syntax features are available.

**Type**: String (semantic version)

**Valid values**:
- `"1.0.0"` - Original UPLC
- `"1.1.0"` - UPLC with `constr` and `case` support

**Example**: `"1.1.0"`

**Note**: Programs using constructors (`constr`) and case expressions (`case`) require UPLC version 1.1.0.

#### `cost_model_params` (optional)

Custom cost model parameters for evaluation. The cost model defines CPU and memory costs for every builtin function and CEK machine operation.

**Type**: Array of integers or `null`

**Format**: Flat array of Int64 integers, ordered according to the parameter name enumeration for the specified `ledger_language`.

**Parameter Counts by Version:**
- PlutusV1: 168 parameters
- PlutusV2: 175 parameters
- PlutusV3: 245 parameters

**CRITICAL**: The parameter array MUST:
- Contain the exact number of parameters for the specified `ledger_language`
- Provide parameters in the correct order matching the ParamName enum
- Use integer values (Int64 range: -9223372036854775808 to 9223372036854775807)

**Default**: If `null` or omitted, the service uses the default mainnet cost model for the specified protocol version and ledger language.

**Obtaining Cost Models:**

Use `cardano-cli` to query current mainnet cost models:
```bash
cardano-cli query protocol-parameters --mainnet | jq '.costModels'
```

Output format:
```json
{
  "PlutusV1": [100788, 420, 1, 1, ...],  // 168 parameters
  "PlutusV2": [100788, 420, 1, 1, ...],  // 175 parameters
  "PlutusV3": [100788, 420, 1, 1, ...]   // 245 parameters
}
```

Extract the array matching your `ledger_language`:
```bash
jq '.costModels.PlutusV3' protocol-params.json
```

**Validation**: The service validates:
- Array length matches expected count for ledger language
- All values are valid Int64 integers
- No missing or extra parameters

**Error Handling**: Invalid parameters return `validation_error`:
- "Expected 245 cost model parameters for PlutusV3, got 168"
- "Cost model parameter at index 42 is out of Int64 range"

### Example Configuration: Protocol v10 with Mainnet Cost Model

```json
{
  "protocol_version": 10,
  "ledger_language": "PlutusV3",
  "uplc_version": "1.1.0",
  "cost_model_params": null
}
```

This configuration evaluates programs using:
- Protocol version 10 (Plomin)
- PlutusV3 ledger language (with all builtins including BLS12-381 and bitwise operations)
- UPLC version 1.1.0 (with constructor support)
- Default mainnet cost model for PlutusV3

### Example Configuration: Historical Protocol Version

```json
{
  "protocol_version": 7,
  "ledger_language": "PlutusV2",
  "uplc_version": "1.0.0",
  "cost_model_params": null
}
```

This configuration simulates the Vasil hard fork environment (PlutusV2 introduction).

### Example Configuration: PlutusV3 with Custom Mainnet Cost Model

```json
{
  "protocol_version": 10,
  "ledger_language": "PlutusV3",
  "uplc_version": "1.1.0",
  "cost_model_params": [
    100788, 420, 1, 1, 1000, 173, 0, 1, 1000, 59957, 4, 1, 11183, 32,
    201305, 8356, 4, 16000, 100, 16000, 100, 16000, 100, 16000, 100,
    16000, 100, 16000, 100, 100, 100, 16000, 100, 94375, 32, 132994, 32,
    61462, 4, 72010, 178, 0, 1, 22151, 32, 91189, 769, 4, 2,
    85848, 123203, 7305, -900, 1716, 549, 57, 85848, 0, 1, 1, 1000,
    42921, 4, 2, 24548, 29498, 38, 1, 898148, 27279, 1, 51775, 558,
    1, 39184, 1000, 60594, 1, 141895, 32, 83150, 32, 15299, 32, 76049,
    1, 13169, 4, 22100, 10, 28999, 74, 1, 28999, 74, 1, 43285, 552,
    1, 44749, 541, 1, 33852, 32, 68246, 32, 72362, 32, 7243, 32,
    7391, 32, 11546, 32, 85848, 123203, 7305, -900, 1716, 549, 57,
    85848, 0, 1, 90434, 519, 0, 1, 74433, 32, 85848, 123203, 7305,
    -900, 1716, 549, 57, 85848, 0, 1, 1, 85848, 123203, 7305, -900,
    1716, 549, 57, 85848, 0, 1, 955506, 213312, 0, 2, 270652, 22588,
    4, 1457325, 64566, 4, 20467, 1, 4, 0, 141992, 32, 100788, 420,
    1, 1, 81663, 32, 59498, 32, 20142, 32, 24588, 32, 20744, 32,
    25933, 32, 24623, 32, 43053543, 10, 53384111, 14333, 10, 43574283,
    26308, 10, 16000, 100, 16000, 100, 962335, 18, 2780678, 6, 442008,
    1, 52538055, 3756, 18, 267929, 18, 76433006, 8868, 18, 52948122,
    18, 1995836, 36, 3227919, 12, 901022, 1, 166917843, 4307, 36,
    284546, 36, 158221314, 26549, 36, 74698472, 36, 333849714, 1,
    254006273, 72, 2174038, 72, 2261318, 64571, 4, 207616, 8310, 4,
    1293828, 28716, 63, 0, 1, 1006041, 43623, 251, 0, 1
  ]
}
```

**Note**: This shows actual mainnet PlutusV3 parameters (245 total). These values are from protocol v10.

### Example: Extracting Cost Models from cardano-cli

```bash
# Query protocol parameters
cardano-cli query protocol-parameters --mainnet > protocol-params.json

# Extract all cost models
jq '.costModels' protocol-params.json > costmodels.json

# Extract PlutusV3 parameters only
jq '.costModels.PlutusV3' protocol-params.json > plutusv3-params.json

# Create config with extracted parameters
cat > my-config.json <<EOF
{
  "protocol_version": 10,
  "ledger_language": "PlutusV3",
  "uplc_version": "1.1.0",
  "cost_model_params": $(cat plutusv3-params.json)
}
EOF
```

### Common Mistakes

**Wrong ledger language:**
```json
{
  "ledger_language": "PlutusV3",
  "cost_model_params": [100788, 420, ...]  // Only 168 params (PlutusV1)
}
```
→ Error: "Expected 245 cost model parameters for PlutusV3, got 168"

**Mixing versions:**
```json
{
  "ledger_language": "PlutusV2",
  "cost_model_params": [...]  // 245 params (PlutusV3)
}
```
→ Error: "Expected 175 cost model parameters for PlutusV2, got 245"

**Including all versions (wrong format):**
```json
{
  "ledger_language": "PlutusV3",
  "cost_model_params": {
    "PlutusV1": [...],
    "PlutusV2": [...],
    "PlutusV3": [...]
  }
}
```
→ Error: "cost_model_params must be an array of integers or null"

**Solution**: Extract only the array for your ledger_language:
```bash
jq '.costModels.PlutusV3' protocol-params.json
```

### Default Values

If no configuration file is provided, the service uses these defaults:

- **`protocol_version`**: `10` (latest stable mainnet)
- **`ledger_language`**: `"PlutusV3"` (latest ledger language)
- **`uplc_version`**: `"1.1.0"` (latest UPLC version)
- **`cost_model_params`**: `null` (mainnet cost model for PlutusV3)

### Validation

The evaluation service validates configuration files and returns an error if:
- Required fields are missing
- Protocol version is not supported
- Ledger language is not available in the specified protocol version
- UPLC version is invalid or not supported
- Cost model parameters are malformed
- Cost model parameters array length does not match ledger language (168/175/245)
- Cost model parameter values are not valid Int64 integers

**Error type**: `validation_error`

### Complete Submission Example

To submit a UPLC program with custom configuration:

```bash
# Generate job ID
JOB_ID=$(uuidgen | tr '[:upper:]' '[:lower:]')

# Write program
scp my-program.uplc.txt benchmarking@host:/benchmarking/input/${JOB_ID}.uplc.txt

# Write configuration
cat > config.json <<EOF
{
  "protocol_version": 10,
  "ledger_language": "PlutusV3",
  "uplc_version": "1.1.0",
  "cost_model_params": null
}
EOF
scp config.json benchmarking@host:/benchmarking/input/${JOB_ID}.config.json

# Poll for results
while [ ! -f /benchmarking/output/${JOB_ID}.result.json ] && \
      [ ! -f /benchmarking/output/${JOB_ID}.error.json ]; do
  sleep 1
done
```

### Cost Model References

**Current Mainnet Cost Models:**
Query using: `cardano-cli query protocol-parameters --mainnet | jq '.costModels'`

**Parameter Ordering:**
Parameter order MUST match the ParamName enumeration:
- PlutusV1: `plutus-ledger-api/src/PlutusLedgerApi/V1/ParamName.hs`
- PlutusV2: `plutus-ledger-api/src/PlutusLedgerApi/V2/ParamName.hs`
- PlutusV3: `plutus-ledger-api/src/PlutusLedgerApi/V3/ParamName.hs`

**DO NOT** manually reorder parameters. Always use:
- cardano-cli output (recommended)
- dump-cost-model-parameters from Plutus repository
- Official protocol parameter updates

**Repository Cost Models (Development):**
- `plutus-core/cost-model/data/builtinCostModelA.json` (nested format, for reference)
- `plutus-core/cost-model/data/builtinCostModelB.json`
- `plutus-core/cost-model/data/builtinCostModelC.json`
- `plutus-core/cost-model/data/cekMachineCosts.json`

Note: Repository files use nested JSON format and may differ from mainnet values.

## JSON Output Format for Successful Evaluations

### File Extension

Successful evaluation results use the `.result.json` file extension and follow the job ID naming convention: `{job_id}.result.json`

### Format

Result files are JSON objects containing raw measurement samples from UPLC program evaluation. Each measurement includes execution time, memory usage, and budget consumption metrics.

### Result Schema

```json
{
  "program_id": "<string>",
  "status": "success",
  "measurements": [
    {
      "cpu_time_ms": <number>,
      "memory_bytes": <number>,
      "cpu_budget": <number>,
      "memory_budget": <number>
    },
    ...
  ]
}
```

### Fields

#### `program_id` (required)

The job identifier (UUID v4) for this evaluation request. This matches the job ID used in the submitted program filename.

**Type**: String (UUID v4 format)

**Example**: `"550e8400-e29b-41d4-a716-446655440000"`

#### `status` (required)

The evaluation status. For successful evaluations, this field is always `"success"`.

**Type**: String (enum)

**Value**: `"success"`

#### `measurements` (required)

An array of raw measurement samples collected during program evaluation. Each program is evaluated multiple times (typically 10-20 iterations) to capture execution variability.

**Type**: Array of measurement objects

**Length**: 10-20 samples (exact count depends on evaluation service configuration)

**Important**: These are **raw samples**, not aggregated statistics. Clients are responsible for computing mean, median, standard deviation, or other statistics from these samples if needed.

### Measurement Object Fields

Each measurement object in the `measurements` array contains four metrics:

#### `cpu_time_ms` (required)

Wall-clock execution time in milliseconds. This measures the actual elapsed time for the CEK machine evaluation.

**Type**: Number (floating-point)

**Unit**: Milliseconds

**Example**: `42.583`

**Note**: This is wall-clock time, not CPU budget units. It reflects actual hardware performance.

#### `memory_bytes` (required)

Peak memory usage during evaluation in bytes. This measures the maximum memory allocated by the CEK machine during execution.

**Type**: Number (integer)

**Unit**: Bytes

**Example**: `4096`

**Note**: This is actual memory usage, not memory budget units.

#### `cpu_budget` (required)

Total CPU budget consumed during evaluation, measured in ExCPU units as defined by the cost model. This is the on-chain execution cost that would be charged for this program.

**Type**: Number (integer)

**Unit**: ExCPU (execution CPU units)

**Example**: `1000000`

**Note**: Budget consumption depends on the cost model parameters specified in the configuration.

#### `memory_budget` (required)

Total memory budget consumed during evaluation, measured in ExMemory units as defined by the cost model. This is the on-chain memory cost that would be charged for this program.

**Type**: Number (integer)

**Unit**: ExMemory (execution memory units)

**Example**: `500000`

**Note**: Budget consumption depends on the cost model parameters specified in the configuration.

### Example Result: Simple Program

```json
{
  "program_id": "550e8400-e29b-41d4-a716-446655440000",
  "status": "success",
  "measurements": [
    {
      "cpu_time_ms": 0.421,
      "memory_bytes": 2048,
      "cpu_budget": 100000,
      "memory_budget": 50000
    },
    {
      "cpu_time_ms": 0.398,
      "memory_bytes": 2048,
      "cpu_budget": 100000,
      "memory_budget": 50000
    },
    {
      "cpu_time_ms": 0.415,
      "memory_bytes": 2048,
      "cpu_budget": 100000,
      "memory_budget": 50000
    },
    {
      "cpu_time_ms": 0.402,
      "memory_bytes": 2048,
      "cpu_budget": 100000,
      "memory_budget": 50000
    },
    {
      "cpu_time_ms": 0.419,
      "memory_bytes": 2048,
      "cpu_budget": 100000,
      "memory_budget": 50000
    },
    {
      "cpu_time_ms": 0.408,
      "memory_bytes": 2048,
      "cpu_budget": 100000,
      "memory_budget": 50000
    },
    {
      "cpu_time_ms": 0.411,
      "memory_bytes": 2048,
      "cpu_budget": 100000,
      "memory_budget": 50000
    },
    {
      "cpu_time_ms": 0.425,
      "memory_bytes": 2048,
      "cpu_budget": 100000,
      "memory_budget": 50000
    },
    {
      "cpu_time_ms": 0.403,
      "memory_bytes": 2048,
      "cpu_budget": 100000,
      "memory_budget": 50000
    },
    {
      "cpu_time_ms": 0.417,
      "memory_bytes": 2048,
      "cpu_budget": 100000,
      "memory_budget": 50000
    }
  ]
}
```

**Observations from this example**:
- 10 measurement samples collected
- `cpu_time_ms` shows variation between runs (0.398 to 0.425 ms)
- `memory_bytes` is consistent (deterministic allocation)
- Budget consumption (`cpu_budget`, `memory_budget`) is deterministic
- Clients should compute statistics: mean CPU time ≈ 0.412 ms, std dev ≈ 0.009 ms

### Example Result: Complex Program

```json
{
  "program_id": "a1b2c3d4-e5f6-4789-a012-3456789abcde",
  "status": "success",
  "measurements": [
    {
      "cpu_time_ms": 125.842,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 123.156,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 127.934,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 124.587,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 126.419,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 122.738,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 128.205,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 125.063,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 124.178,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 126.891,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 123.542,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 127.319,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 125.684,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 124.926,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    },
    {
      "cpu_time_ms": 126.437,
      "memory_bytes": 524288,
      "cpu_budget": 50000000,
      "memory_budget": 10000000
    }
  ]
}
```

**Observations from this example**:
- 15 measurement samples collected (service may vary sample count)
- Higher CPU time for complex program (~125 ms vs ~0.4 ms)
- Higher memory usage (512 KB vs 2 KB)
- Significantly higher budget consumption (50M ExCPU vs 100K ExCPU)
- Execution time still varies between runs (122.7 to 128.2 ms)

### Raw Samples vs. Aggregated Statistics

**Important**: Result files contain **raw measurement samples**, not pre-computed statistics.

Clients must perform their own statistical analysis:

**Sample Statistical Analysis** (using Example 1 data):
```
Mean CPU time:    0.412 ms
Median CPU time:  0.412 ms
Min CPU time:     0.398 ms
Max CPU time:     0.425 ms
Std deviation:    0.009 ms
```

**Rationale**: Raw samples provide maximum flexibility for analysis. Different use cases may require:
- Mean and standard deviation for performance benchmarking
- Median and percentiles for understanding typical behavior
- Min/max for worst-case analysis
- Distribution analysis for detecting anomalies

### Usage Notes

- Results are written to `/benchmarking/output/{job_id}.result.json` when evaluation completes successfully
- Result files remain available until cleanup (see retention policy)
- Budget values are deterministic for a given program and cost model
- Wall-clock times (`cpu_time_ms`, `memory_bytes`) may vary between runs due to system load
- Multiple samples enable statistical confidence in measurements
- Budget consumption is independent of hardware performance (cost model is abstract)
- Clients should parse JSON and extract measurements array for analysis

## JSON Output Format for Error Cases

### File Extension

Error results use the `.error.json` file extension and follow the job ID naming convention: `{job_id}.error.json`

### Format

Error files are JSON objects containing diagnostic information when program submission, validation, or evaluation fails. Error messages are designed to be human-readable and actionable to help clients debug issues.

### Error Schema

```json
{
  "program_id": "<string>",
  "status": "error",
  "error_type": "<string>",
  "error_message": "<string>"
}
```

### Fields

#### `program_id` (required)

The job identifier (UUID v4) for this evaluation request. This matches the job ID used in the submitted program filename.

**Type**: String (UUID v4 format)

**Example**: `"550e8400-e29b-41d4-a716-446655440000"`

#### `status` (required)

The evaluation status. For failed evaluations, this field is always `"error"`.

**Type**: String (enum)

**Value**: `"error"`

#### `error_type` (required)

The category of error that occurred. This enables programmatic error handling and filtering.

**Type**: String (enum)

**Valid values**:
- `"syntax_error"` - Program cannot be parsed (invalid UPLC syntax)
- `"validation_error"` - Program parsed but violates validation rules
- `"evaluation_error"` - Program is valid but evaluation failed at runtime
- `"timeout"` - Program evaluation exceeded time limit

**Example**: `"syntax_error"`

#### `error_message` (required)

A human-readable description of the error with actionable guidance for resolution.

**Type**: String

**Characteristics**:
- Clear and descriptive
- Identifies the specific problem
- Provides location information when available (line/column numbers for syntax errors)
- Suggests corrective action when possible
- Avoids technical jargon where appropriate

**Example**: `"Syntax error at line 3, column 15: Expected closing parenthesis ')' but found 'con'"`

### Error Types

#### `syntax_error`

The program file could not be parsed. This indicates invalid UPLC syntax.

**Common causes**:
- Mismatched parentheses or brackets
- Invalid version number format
- Typos in keywords (`lam`, `con`, `builtin`, etc.)
- Invalid constant types or values
- Malformed flat-encoded binary
- Free variables (unbound variable names)

**Resolution**: Review the program syntax against plutus-core-spec.pdf and correct parsing errors.

#### `validation_error`

The program parsed successfully but violates semantic validation rules.

**Common causes**:
- Unapplied lambda abstractions (program evaluates to a function)
- Unapplied builtin functions (insufficient arguments)
- Invalid configuration parameters (unsupported protocol version, incompatible ledger language)
- Type mismatches in builtin applications
- Invalid constructor tags or case expression arity

**Resolution**: Ensure the program is fully applied and evaluates to a value. Verify configuration parameters are valid.

#### `evaluation_error`

The program is syntactically and semantically valid but encountered a runtime error during evaluation.

**Common causes**:
- Division by zero
- Out-of-bounds list access
- Type errors in builtin operations (e.g., applying `addInteger` to a bytestring)
- Stack overflow from excessive recursion
- Explicit error term evaluation `(error)`

**Resolution**: Review program logic for runtime errors. Test with simplified inputs to isolate the failing operation.

#### `timeout`

Program evaluation exceeded the maximum allowed execution time.

**Common causes**:
- Infinite loops or unbounded recursion
- Extremely large input data structures
- Computationally intensive operations without sufficient optimization

**Resolution**: Optimize the program to reduce complexity. Break large computations into smaller batches. Consider algorithmic improvements.

### Example Error: Syntax Error

```json
{
  "program_id": "f7e8d9c0-b1a2-4567-8901-234567890abc",
  "status": "error",
  "error_type": "syntax_error",
  "error_message": "Syntax error at line 3, column 15: Expected closing parenthesis ')' but found 'con'. Check for missing or extra parentheses in the program structure."
}
```

**Explanation**: The parser encountered a syntax error where a closing parenthesis was expected but found a constant declaration instead. This typically indicates mismatched parentheses.

### Example Error: Validation Error (Unapplied Lambda)

```json
{
  "program_id": "a9b8c7d6-e5f4-4321-9876-543210fedcba",
  "status": "error",
  "error_type": "validation_error",
  "error_message": "Validation failed: Program evaluates to an unapplied lambda abstraction. Programs must be fully applied and evaluate to values, not functions. Ensure all lambda abstractions receive their required arguments."
}
```

**Explanation**: The program is syntactically correct but violates the validation rule that programs must evaluate to values. This program evaluates to a function (lambda), which is not allowed.

### Example Error: Validation Error (Configuration)

```json
{
  "program_id": "12345678-abcd-4ef0-9876-1234567890ab",
  "status": "error",
  "error_type": "validation_error",
  "error_message": "Invalid configuration: Ledger language 'PlutusV3' is not available in protocol version 7. PlutusV3 requires protocol version 9 or higher. Use 'PlutusV2' for protocol version 7, or upgrade protocol_version to 9+."
}
```

**Explanation**: The configuration specifies an incompatible combination of protocol version and ledger language. PlutusV3 was introduced in protocol version 9 (Chang hard fork) and is not available in earlier versions.

### Example Error: Evaluation Error (Builtin Failure)

```json
{
  "program_id": "11111111-2222-4333-8444-555555555555",
  "status": "error",
  "error_type": "evaluation_error",
  "error_message": "Evaluation failed: Builtin 'divideInteger' failed with division by zero. Check program logic to ensure divisor is non-zero before division operations."
}
```

**Explanation**: The program is valid but failed during evaluation when attempting to divide by zero. The error message identifies the specific builtin that failed and the cause.

### Example Error: Timeout

```json
{
  "program_id": "99999999-8888-4777-8666-555555555555",
  "status": "error",
  "error_type": "timeout",
  "error_message": "Evaluation timeout: Program exceeded maximum execution time of 10 minutes. This may indicate an infinite loop, unbounded recursion, or excessive computational complexity. Review program logic for termination conditions and optimize algorithmic complexity."
}
```

**Explanation**: The program did not complete evaluation within the allowed time limit. This suggests the program may have an infinite loop or is computationally too expensive.

### Error Message Guidelines

All error messages follow these principles:

1. **Identify the problem**: State what went wrong clearly and specifically
2. **Provide context**: Include location information (line/column for syntax errors, builtin name for evaluation errors)
3. **Explain the cause**: Describe why the error occurred
4. **Suggest resolution**: Offer actionable guidance on how to fix the issue
5. **Be respectful**: Avoid condescending language; assume the user is capable

**Good error message example**:
```
"Syntax error at line 5, column 23: Invalid constant type 'int'.
Did you mean 'integer'? Valid constant types are: integer, bytestring,
string, unit, bool, data, list, pair."
```

**Bad error message example**:
```
"Parse error: unexpected token at 5:23"
```

### Usage Notes

- Error files are written to `/benchmarking/output/{job_id}.error.json` when evaluation fails
- Only one of `.result.json` or `.error.json` will be written for each job
- Clients should check for both result and error files when polling for completion
- Error messages are designed to be shown directly to users without additional processing
- The `error_type` field enables programmatic filtering and categorization of errors
- For persistent errors, clients should verify their UPLC syntax against plutus-core-spec.pdf
- Configuration errors can be resolved by checking protocol version compatibility tables

## SSH Access and Authentication

### Overview

The UPLC benchmarking environment is accessed via SSH using key-based authentication. Clients connect to a dedicated benchmarking server, transfer program files to the input directory, and retrieve results from the output directory.

### Connection Details

**Hostname**: `benchmarking.plutus.internal` (placeholder - actual hostname to be provided upon deployment)

**Port**: `22` (standard SSH port)

**Username**: `benchmarking`

**Authentication**: SSH public key authentication (password authentication disabled for security)

**Note**: The actual hostname, port, and username will be provided to authorized clients after the benchmarking environment is deployed. Contact the Plutus team for access credentials.

### Connection Examples

#### Basic SSH Connection

```bash
# Connect to the benchmarking server
ssh -i ~/.ssh/id_ed25519_plutus benchmarking@benchmarking.plutus.internal

# Connection with custom port (if non-standard port is used)
ssh -i ~/.ssh/id_ed25519_plutus -p 2222 benchmarking@benchmarking.plutus.internal
```

#### SSH Config File Setup

For convenience, add an entry to your `~/.ssh/config` file:

```
Host plutus-benchmarking
    HostName benchmarking.plutus.internal
    Port 22
    User benchmarking
    IdentityFile ~/.ssh/id_ed25519_plutus
    ServerAliveInterval 60
    ServerAliveCountMax 3
```

Then connect using the alias:

```bash
ssh plutus-benchmarking
```

### File Transfer

Use `scp` or `sftp` to transfer files to and from the benchmarking server.

#### Uploading Program Files (SCP)

```bash
# Upload textual UPLC program
scp -i ~/.ssh/id_ed25519_plutus \
    my-program.uplc.txt \
    benchmarking@benchmarking.plutus.internal:/benchmarking/input/550e8400-e29b-41d4-a716-446655440000.uplc.txt

# Upload flat-encoded program
scp -i ~/.ssh/id_ed25519_plutus \
    my-program.uplc.flat \
    benchmarking@benchmarking.plutus.internal:/benchmarking/input/550e8400-e29b-41d4-a716-446655440000.uplc.flat

# Upload configuration file
scp -i ~/.ssh/id_ed25519_plutus \
    config.json \
    benchmarking@benchmarking.plutus.internal:/benchmarking/input/550e8400-e29b-41d4-a716-446655440000.config.json
```

If using the SSH config alias:

```bash
scp my-program.uplc.txt plutus-benchmarking:/benchmarking/input/550e8400-e29b-41d4-a716-446655440000.uplc.txt
```

#### Downloading Result Files (SCP)

```bash
# Download result file
scp -i ~/.ssh/id_ed25519_plutus \
    benchmarking@benchmarking.plutus.internal:/benchmarking/output/550e8400-e29b-41d4-a716-446655440000.result.json \
    ./results/

# Download error file (if evaluation failed)
scp -i ~/.ssh/id_ed25519_plutus \
    benchmarking@benchmarking.plutus.internal:/benchmarking/output/550e8400-e29b-41d4-a716-446655440000.error.json \
    ./errors/
```

#### Using SFTP for Interactive Transfer

```bash
# Start SFTP session
sftp -i ~/.ssh/id_ed25519_plutus benchmarking@benchmarking.plutus.internal

# SFTP commands
sftp> cd /benchmarking/input
sftp> put my-program.uplc.txt 550e8400-e29b-41d4-a716-446655440000.uplc.txt
sftp> cd /benchmarking/output
sftp> get 550e8400-e29b-41d4-a716-446655440000.result.json
sftp> exit
```

### Directory Permissions

#### Input Directory (`/benchmarking/input/`)

**Permissions for clients**:
- **Read**: Yes - clients can list files they submitted
- **Write**: Yes - clients can upload program and configuration files
- **Execute**: Yes - clients can traverse the directory

**Restrictions**:
- Clients can only read/delete their own files
- Clients cannot modify files owned by other users
- File size limit: 10 MB per file (enforced at upload)

**Purpose**: Receive UPLC programs and configurations from clients for evaluation.

#### Output Directory (`/benchmarking/output/`)

**Permissions for clients**:
- **Read**: Yes - clients can download result and error files
- **Write**: No - only the evaluation service can write to this directory
- **Execute**: Yes - clients can traverse the directory

**Restrictions**:
- Clients have read-only access to output directory
- Clients can only read result/error files corresponding to their submitted jobs
- Files are automatically cleaned up after retention period (see cleanup policy below)

**Purpose**: Provide evaluation results and error information to clients.

#### Home Directory (`/home/benchmarking/`)

Clients have a shared home directory with limited quota:
- **Quota**: 100 MB per user session
- **Purpose**: Temporary workspace for preparing files before submission
- **Cleanup**: Files in home directory are not automatically cleaned up; clients should manage their own workspace

### Security Considerations

#### Connection Security

- **Encryption**: All SSH connections use strong encryption (AES-256 or ChaCha20-Poly1305)
- **Host key verification**: Clients should verify the server's host key fingerprint on first connection
- **Key management**: Private keys should be protected with filesystem permissions (chmod 600)

**Host key fingerprint** (to be provided upon deployment):
```
ED25519: SHA256:XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX (placeholder)
RSA:     SHA256:XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX (placeholder)
```

Verify the host key fingerprint on first connection to prevent man-in-the-middle attacks.

#### File Security

- **File ownership**: All submitted files are owned by the submitting user
- **Isolation**: Clients cannot access files submitted by other users
- **Validation**: The evaluation service validates all inputs to prevent code injection attacks
- **Sandboxing**: Program evaluation runs in an isolated environment with resource limits

#### Credential Security

- **Private key protection**: Never share your private key or commit it to version control
- **Key rotation**: Rotate SSH keys periodically (recommended: every 6-12 months)
- **Compromised keys**: If your private key is compromised, notify the Plutus team immediately for key revocation

### Troubleshooting

#### Connection Issues

**Problem**: `Permission denied (publickey)`

**Solution**:
1. Verify your public key has been registered with the Plutus team
2. Check that you're using the correct private key file (`-i` option)
3. Ensure private key has correct permissions: `chmod 600 ~/.ssh/id_ed25519_plutus`
4. Verify you're connecting as the correct user (`benchmarking@...`)

**Problem**: `Connection timed out`

**Solution**:
1. Check network connectivity to the benchmarking server
2. Verify the hostname and port are correct
3. Check if your firewall is blocking outbound SSH connections
4. Contact the Plutus team if the server is unreachable

#### File Transfer Issues

**Problem**: `scp: /benchmarking/input/...: Permission denied`

**Solution**:
1. Verify you have write permissions to the input directory
2. Check that the file path is correct (absolute path required)
3. Ensure you're not exceeding file size limits (10 MB)

**Problem**: `File not found` when downloading results

**Solution**:
1. Verify the job ID is correct
2. Check if the evaluation has completed (result/error file may not exist yet)
3. Confirm you're checking the output directory (not input directory)
4. Check if the result file has been cleaned up (see retention policy)

### Contact and Support

For SSH access issues, credential problems, or questions about connection requirements:
- **Email**: plutus-benchmarking-support@example.com (placeholder)
- **Issue tracker**: github.com/IntersectMBO/plutus-private/issues (for authorized users)

**Before contacting support**:
1. Verify your public key has been registered
2. Test basic SSH connectivity: `ssh -v` for verbose output
3. Check system-wide service status (if available)

## File-Based Workflow and Job Lifecycle

### Overview

The UPLC benchmarking interface uses an **asynchronous file-based workflow**. Clients submit programs by uploading files to the input directory, and the evaluation service processes these files in the background, writing results to the output directory when complete.

This section describes the complete job lifecycle from submission to result retrieval.

### Job States

Each submitted job progresses through the following states:

#### 1. Submitted

**Description**: Program file has been uploaded to the input directory, but evaluation has not started yet.

**Detection**: Program file exists in `/benchmarking/input/`, but no corresponding result or error file exists in `/benchmarking/output/`.

**Duration**: Typically seconds to minutes, depending on system load and queue depth.

**Client action**: Wait for processing to begin (no action required).

#### 2. Processing

**Description**: The evaluation service has picked up the job and is actively evaluating the program.

**Detection**: Program file exists in input directory, evaluation is underway, but no result/error file has appeared yet.

**Duration**: Seconds to minutes for typical programs. Up to 10 minutes for complex programs (timeout limit).

**Client action**: Poll the output directory for result/error files.

#### 3. Completed (Success)

**Description**: Program evaluation finished successfully. Measurement samples are available.

**Detection**: `/benchmarking/output/{job_id}.result.json` file exists.

**Final state**: Yes - job will not change state again.

**Client action**: Download and process the result file. Delete the program file from input directory if no longer needed.

#### 4. Failed (Error)

**Description**: Program evaluation encountered an error (syntax, validation, evaluation, or timeout).

**Detection**: `/benchmarking/output/{job_id}.error.json` file exists.

**Final state**: Yes - job will not change state again.

**Client action**: Download and analyze the error file. Fix the issue and resubmit if needed.

### Job State Diagram

```
Submitted → Processing → Completed (success)
                      → Failed (error)
```

### Step-by-Step Workflow

#### Step 1: Generate Job ID

Generate a unique UUID v4 identifier for your job:

```bash
# Linux/macOS
JOB_ID=$(uuidgen | tr '[:upper:]' '[:lower:]')

# Alternative using Python
JOB_ID=$(python3 -c "import uuid; print(str(uuid.uuid4()))")

# Verify format (should be xxxxxxxx-xxxx-4xxx-xxxx-xxxxxxxxxxxx)
echo "Job ID: $JOB_ID"
```

#### Step 2: Prepare Program File

Prepare your UPLC program in either textual or flat-encoded format:

**Textual format** (`.uplc.txt`):
```bash
# Example: Simple program file
cat > program.uplc.txt <<'EOF'
(program 1.0.0
  [ [ (builtin addInteger) (con integer 21) ] (con integer 21) ]
)
EOF
```

**Flat-encoded format** (`.uplc.flat`):
```bash
# Convert textual to flat-encoded
uplc convert --from textual --to flat -i program.uplc.txt -o program.uplc.flat
```

#### Step 3: Prepare Configuration (Optional)

If you need custom version parameters, create a configuration file:

```bash
# Example configuration for protocol v10, PlutusV3
cat > config.json <<'EOF'
{
  "protocol_version": 10,
  "ledger_language": "PlutusV3",
  "uplc_version": "1.1.0",
  "cost_model_params": null
}
EOF
```

**Note**: If you omit the configuration file, the service uses default values (protocol v10, PlutusV3, UPLC 1.1.0).

#### Step 4: Upload Files via SSH

Upload your program (and optional configuration) to the input directory:

```bash
# Upload program file
scp program.uplc.txt plutus-benchmarking:/benchmarking/input/${JOB_ID}.uplc.txt

# Upload configuration (optional)
scp config.json plutus-benchmarking:/benchmarking/input/${JOB_ID}.config.json

# Alternative: Upload flat-encoded program
scp program.uplc.flat plutus-benchmarking:/benchmarking/input/${JOB_ID}.uplc.flat
```

**Note**: Use the SSH alias `plutus-benchmarking` if you configured it in `~/.ssh/config`, or use the full connection string with `-i` flag.

#### Step 5: Poll for Completion

Wait for the evaluation service to process the job and write results:

```bash
# Simple polling loop (checks every 5 seconds)
while [ ! -f /benchmarking/output/${JOB_ID}.result.json ] && \
      [ ! -f /benchmarking/output/${JOB_ID}.error.json ]; do
  echo "Waiting for job ${JOB_ID} to complete..."
  sleep 5
done

echo "Job completed!"
```

**Better approach**: Poll with exponential backoff to reduce load on the system:

```bash
# Polling with exponential backoff
WAIT_TIME=1
MAX_WAIT=60
TOTAL_WAIT=0
MAX_TOTAL_WAIT=660  # 11 minutes (10 min eval + 1 min buffer)

while [ $TOTAL_WAIT -lt $MAX_TOTAL_WAIT ]; do
  # Check if result or error file exists (via SSH)
  if ssh plutus-benchmarking "[ -f /benchmarking/output/${JOB_ID}.result.json ] || \
                                [ -f /benchmarking/output/${JOB_ID}.error.json ]"; then
    echo "Job completed after ${TOTAL_WAIT} seconds"
    break
  fi

  echo "Waiting ${WAIT_TIME} seconds... (total: ${TOTAL_WAIT}s)"
  sleep $WAIT_TIME
  TOTAL_WAIT=$((TOTAL_WAIT + WAIT_TIME))

  # Exponential backoff: double wait time, cap at MAX_WAIT
  WAIT_TIME=$((WAIT_TIME * 2))
  if [ $WAIT_TIME -gt $MAX_WAIT ]; then
    WAIT_TIME=$MAX_WAIT
  fi
done

if [ $TOTAL_WAIT -ge $MAX_TOTAL_WAIT ]; then
  echo "Timeout: Job did not complete within expected time"
  exit 1
fi
```

#### Step 6: Download Results

Download the result or error file from the output directory:

```bash
# Check which file exists and download it
if ssh plutus-benchmarking "[ -f /benchmarking/output/${JOB_ID}.result.json ]"; then
  # Success case: download result
  scp plutus-benchmarking:/benchmarking/output/${JOB_ID}.result.json ./results/${JOB_ID}.result.json
  echo "Success! Results downloaded to ./results/${JOB_ID}.result.json"
elif ssh plutus-benchmarking "[ -f /benchmarking/output/${JOB_ID}.error.json ]"; then
  # Error case: download error
  scp plutus-benchmarking:/benchmarking/output/${JOB_ID}.error.json ./errors/${JOB_ID}.error.json
  echo "Evaluation failed. Error details downloaded to ./errors/${JOB_ID}.error.json"
  exit 1
else
  echo "No result or error file found (unexpected state)"
  exit 1
fi
```

#### Step 7: Process and Analyze Results

Parse the result JSON and extract metrics:

```bash
# Parse result JSON and extract measurements
jq '.measurements[] | {cpu_time_ms, cpu_budget, memory_budget}' ./results/${JOB_ID}.result.json

# Compute statistics (mean CPU time)
jq '[.measurements[].cpu_time_ms] | add / length' ./results/${JOB_ID}.result.json

# Check budget consumption
jq '.measurements[0] | {cpu_budget, memory_budget}' ./results/${JOB_ID}.result.json
```

### Job Completion Detection

The evaluation service signals job completion by writing a file to the output directory. Clients detect completion by polling for these files.

#### Completion Signals

**Success**: `/benchmarking/output/{job_id}.result.json` file appears

**Failure**: `/benchmarking/output/{job_id}.error.json` file appears

**Important**: Only ONE of these files will be written per job. Check for both when polling.

#### Polling Strategy

**Basic polling** (check every N seconds):
```bash
# Simple approach: check every 5 seconds
while ! ssh plutus-benchmarking "[ -f /benchmarking/output/${JOB_ID}.result.json ] || \
                                  [ -f /benchmarking/output/${JOB_ID}.error.json ]"; do
  sleep 5
done
```

**Exponential backoff polling** (recommended):
```bash
# Start with 1 second, double each iteration, cap at 60 seconds
# This reduces load on the server for long-running jobs
WAIT_TIME=1
while ! ssh plutus-benchmarking "[ -f /benchmarking/output/${JOB_ID}.result.json ] || \
                                  [ -f /benchmarking/output/${JOB_ID}.error.json ]"; do
  sleep $WAIT_TIME
  WAIT_TIME=$((WAIT_TIME * 2))
  [ $WAIT_TIME -gt 60 ] && WAIT_TIME=60
done
```

**Timeout protection**:
```bash
# Abort polling after 11 minutes (10 min eval timeout + 1 min buffer)
ELAPSED=0
MAX_WAIT=660
while [ $ELAPSED -lt $MAX_WAIT ]; do
  if ssh plutus-benchmarking "[ -f /benchmarking/output/${JOB_ID}.result.json ] || \
                                [ -f /benchmarking/output/${JOB_ID}.error.json ]"; then
    break
  fi
  sleep 5
  ELAPSED=$((ELAPSED + 5))
done

if [ $ELAPSED -ge $MAX_WAIT ]; then
  echo "Error: Job did not complete within timeout period"
  exit 1
fi
```

#### Batch Job Polling

For batch submissions, poll for multiple jobs efficiently:

```bash
# List of job IDs to monitor
JOB_IDS=("job1-uuid" "job2-uuid" "job3-uuid")

# Track completed jobs
COMPLETED=0
TOTAL=${#JOB_IDS[@]}

while [ $COMPLETED -lt $TOTAL ]; do
  for JOB_ID in "${JOB_IDS[@]}"; do
    # Skip already completed jobs
    [ -f "./results/${JOB_ID}.result.json" ] && continue
    [ -f "./errors/${JOB_ID}.error.json" ] && continue

    # Check for completion
    if ssh plutus-benchmarking "[ -f /benchmarking/output/${JOB_ID}.result.json ]"; then
      scp plutus-benchmarking:/benchmarking/output/${JOB_ID}.result.json ./results/
      COMPLETED=$((COMPLETED + 1))
      echo "Job ${JOB_ID} completed successfully ($COMPLETED/$TOTAL)"
    elif ssh plutus-benchmarking "[ -f /benchmarking/output/${JOB_ID}.error.json ]"; then
      scp plutus-benchmarking:/benchmarking/output/${JOB_ID}.error.json ./errors/
      COMPLETED=$((COMPLETED + 1))
      echo "Job ${JOB_ID} failed ($COMPLETED/$TOTAL)"
    fi
  done

  # Wait before next poll cycle
  [ $COMPLETED -lt $TOTAL ] && sleep 10
done

echo "All jobs completed: $COMPLETED/$TOTAL"
```

### Complete Example Bash Script

Here is a complete, production-ready script for submitting a UPLC program and retrieving results:

```bash
#!/bin/bash
set -euo pipefail

# Configuration
SSH_HOST="plutus-benchmarking"  # SSH config alias
INPUT_DIR="/benchmarking/input"
OUTPUT_DIR="/benchmarking/output"
PROGRAM_FILE="$1"  # First argument: path to UPLC program
CONFIG_FILE="${2:-}"  # Second argument (optional): path to config JSON

# Validate arguments
if [ -z "$PROGRAM_FILE" ]; then
  echo "Usage: $0 <program-file> [config-file]"
  exit 1
fi

if [ ! -f "$PROGRAM_FILE" ]; then
  echo "Error: Program file not found: $PROGRAM_FILE"
  exit 1
fi

# Generate unique job ID
JOB_ID=$(uuidgen | tr '[:upper:]' '[:lower:]')
echo "Job ID: $JOB_ID"

# Determine file extension from program file
PROGRAM_EXT="${PROGRAM_FILE##*.}"
if [ "$PROGRAM_EXT" = "txt" ]; then
  REMOTE_PROGRAM="${JOB_ID}.uplc.txt"
elif [ "$PROGRAM_EXT" = "flat" ]; then
  REMOTE_PROGRAM="${JOB_ID}.uplc.flat"
else
  echo "Error: Program file must have .txt or .flat extension"
  exit 1
fi

# Create local output directories
mkdir -p results errors

echo "Uploading program file..."
scp "$PROGRAM_FILE" "${SSH_HOST}:${INPUT_DIR}/${REMOTE_PROGRAM}"

# Upload configuration if provided
if [ -n "$CONFIG_FILE" ]; then
  if [ ! -f "$CONFIG_FILE" ]; then
    echo "Error: Config file not found: $CONFIG_FILE"
    exit 1
  fi
  echo "Uploading configuration file..."
  scp "$CONFIG_FILE" "${SSH_HOST}:${INPUT_DIR}/${JOB_ID}.config.json"
fi

echo "Job submitted. Waiting for evaluation to complete..."

# Poll for completion with exponential backoff
WAIT_TIME=1
MAX_WAIT=60
TOTAL_WAIT=0
MAX_TOTAL_WAIT=660  # 11 minutes

while [ $TOTAL_WAIT -lt $MAX_TOTAL_WAIT ]; do
  # Check for result or error file
  if ssh "$SSH_HOST" "[ -f ${OUTPUT_DIR}/${JOB_ID}.result.json ]"; then
    echo "Evaluation completed successfully!"
    scp "${SSH_HOST}:${OUTPUT_DIR}/${JOB_ID}.result.json" "./results/${JOB_ID}.result.json"

    # Display summary
    echo ""
    echo "=== Result Summary ==="
    echo "Program ID: $JOB_ID"
    echo "Sample count: $(jq '.measurements | length' ./results/${JOB_ID}.result.json)"
    echo "Mean CPU time: $(jq '[.measurements[].cpu_time_ms] | add / length' ./results/${JOB_ID}.result.json) ms"
    echo "CPU budget: $(jq '.measurements[0].cpu_budget' ./results/${JOB_ID}.result.json) ExCPU"
    echo "Memory budget: $(jq '.measurements[0].memory_budget' ./results/${JOB_ID}.result.json) ExMemory"
    echo ""
    echo "Full results: ./results/${JOB_ID}.result.json"

    exit 0
  elif ssh "$SSH_HOST" "[ -f ${OUTPUT_DIR}/${JOB_ID}.error.json ]"; then
    echo "Evaluation failed!"
    scp "${SSH_HOST}:${OUTPUT_DIR}/${JOB_ID}.error.json" "./errors/${JOB_ID}.error.json"

    # Display error details
    echo ""
    echo "=== Error Details ==="
    echo "Error type: $(jq -r '.error_type' ./errors/${JOB_ID}.error.json)"
    echo "Error message:"
    jq -r '.error_message' ./errors/${JOB_ID}.error.json
    echo ""
    echo "Full error details: ./errors/${JOB_ID}.error.json"

    exit 1
  fi

  # Wait with exponential backoff
  sleep $WAIT_TIME
  TOTAL_WAIT=$((TOTAL_WAIT + WAIT_TIME))

  # Double wait time, cap at MAX_WAIT
  WAIT_TIME=$((WAIT_TIME * 2))
  [ $WAIT_TIME -gt $MAX_WAIT ] && WAIT_TIME=$MAX_WAIT

  # Progress indicator
  echo "Still waiting... (${TOTAL_WAIT}s elapsed)"
done

# Timeout case
echo "Error: Job did not complete within timeout period (${MAX_TOTAL_WAIT}s)"
echo "The job may still be processing. Check manually:"
echo "  ssh $SSH_HOST ls -la ${OUTPUT_DIR}/${JOB_ID}.*"
exit 1
```

**Usage examples**:
```bash
# Submit textual program with default configuration
./submit-program.sh my-program.uplc.txt

# Submit flat-encoded program with custom configuration
./submit-program.sh my-program.uplc.flat my-config.json

# Submit textual program with protocol v7 configuration
./submit-program.sh validator.uplc.txt protocol-v7-config.json
```

### Cleanup and Retention Policy

#### Input Directory Cleanup

**Client responsibility**: Clients are responsible for cleaning up program and configuration files from the input directory.

**Recommendation**: Delete input files after receiving results to conserve space and quota.

```bash
# Clean up input files after successful evaluation
ssh plutus-benchmarking "rm -f ${INPUT_DIR}/${JOB_ID}.uplc.txt"
ssh plutus-benchmarking "rm -f ${INPUT_DIR}/${JOB_ID}.config.json"
```

**Automatic cleanup**: The service does NOT automatically delete input files. Abandoned input files may count against your directory quota.

#### Output Directory Retention

**Retention period**: Result and error files are retained for **7 days** after creation.

**Automatic cleanup**: The evaluation service automatically deletes result/error files older than 7 days.

**Warning period**: Files approaching the retention limit (6 days old) may be flagged with a warning suffix (implementation-dependent).

**Recommendation**: Download and archive result files within 7 days of submission.

#### Quota Management

**Per-client quotas**:
- **Input directory**: No specific file count limit, but 10 MB per file limit applies
- **Output directory**: Results are cleaned up automatically after 7 days
- **Home directory**: 100 MB quota per user session

**Quota enforcement**: If a client exceeds quota, new file uploads will be rejected with an error message.

**Checking quota**:
```bash
# Check disk usage in home directory
ssh plutus-benchmarking "du -sh ~"

# Count pending jobs in input directory
ssh plutus-benchmarking "ls -1 ${INPUT_DIR}/*.uplc.* | wc -l"
```

### Best Practices

#### Efficient Batch Processing

**Submit in batches**: Instead of submitting one job at a time, submit batches of 50-100 programs to maximize throughput.

**Parallel uploads**: Use parallel SCP or rsync for faster batch uploads:
```bash
# Upload multiple programs in parallel
for PROGRAM in programs/*.uplc.txt; do
  JOB_ID=$(uuidgen | tr '[:upper:]' '[:lower:]')
  scp "$PROGRAM" plutus-benchmarking:/benchmarking/input/${JOB_ID}.uplc.txt &
done
wait  # Wait for all uploads to complete
```

**Batch polling**: Check multiple jobs in a single SSH session to reduce connection overhead.

#### Error Handling

**Retry transient errors**: Some errors (network issues, temporary service unavailability) may be transient. Implement retry logic with exponential backoff.

**Validate programs locally**: Before submitting, validate UPLC syntax locally using the `uplc` executable to catch syntax errors early.

**Monitor error rates**: Track error types to identify systematic issues (e.g., invalid configuration, unapplied programs).

#### Resource Management

**Use exponential backoff polling**: Start with short poll intervals (1-2 seconds) and increase exponentially to reduce server load.

**Clean up regularly**: Delete old input files and download results promptly to conserve quota.

#### Debugging and Monitoring

**Log job IDs**: Maintain a log of submitted job IDs for tracking and debugging:
```bash
echo "$JOB_ID,$PROGRAM_FILE,$(date -Iseconds)" >> submission-log.csv
```

**Check service status**: Before large batch submissions, verify the service is operational:
```bash
ssh plutus-benchmarking "ls -la /benchmarking/output/" | tail -5
```

**Monitor completion rates**: Track how many jobs complete successfully vs. fail to identify issues early.

**Save error logs**: Keep error files for analysis to identify common mistakes in program generation.

