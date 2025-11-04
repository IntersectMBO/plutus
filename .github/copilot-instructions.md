# Plutus Core Development Instructions

Always reference these instructions first and fallback to search or bash commands only when you encounter unexpected information that does not match the info here.

## Critical Development Environment Requirements

**MANDATORY: You MUST use Nix for development.** All builds and tests require the Nix environment. Do not attempt to build without Nix - it will fail due to missing dependencies and specific toolchain requirements.

### Nix Environment Setup

Install Nix first if not available:
```bash
curl -L https://nixos.org/nix/install | sh
```

Enter the development shell:
```bash
nix develop --no-warn-dirty --accept-flake-config
```

Your prompt will change to indicate you're in the Nix shell environment. This shell provides all required tools including:
- Correct GHC version with all Haskell dependencies
- Cabal build tool
- Haskell Language Server (HLS)
- Pre-commit hooks and formatting tools
- Documentation build tools

## Building the Project

### Essential Pre-Build Steps
```bash
# Always run these before building
cabal update
```

### Primary Build Commands

**CRITICAL BUILD TIMING - NEVER CANCEL BUILDS:**

Build the core library (15-30 minutes):
```bash
cabal build plutus-core  # NEVER CANCEL - takes 15-30 minutes, timeout: 45+ minutes
```

Build all packages (45-90 minutes):
```bash
cabal build all  # NEVER CANCEL - takes 45-90 minutes, timeout: 120+ minutes
```

Build specific packages:
```bash
cabal build plutus-tx           # 10-20 minutes
cabal build plutus-ledger-api   # 10-15 minutes  
cabal build plutus-tx-plugin    # 15-25 minutes
cabal build cardano-constitution # 5-10 minutes
cabal build plutus-executables  # 10-15 minutes
```

### Built Executables

The build produces these command-line tools:
```bash
cabal run plutus          # Plutus Core evaluator and tools
cabal run pir             # Plutus IR tools
cabal run plc             # Plutus Core compiler  
cabal run uplc            # Untyped Plutus Core tools
```

Example: Evaluate a Plutus Core program:
```bash
cabal run plc evaluate -- -h    # Show help for evaluation options
```

### Alternative GHC Versions

The project supports multiple GHC versions. Use specific shells:
```bash
nix develop --no-warn-dirty --accept-flake-config .#ghc96   # Primary (default)
nix develop --no-warn-dirty --accept-flake-config .#ghc98   # Alternative
nix develop --no-warn-dirty --accept-flake-config .#ghc910  # Alternative
```

## Testing

### Test Suite Execution

**CRITICAL TESTING TIMING - NEVER CANCEL TESTS:**

Run all tests (30-60 minutes):
```bash
cabal test all  # NEVER CANCEL - takes 30-60 minutes, timeout: 90+ minutes
```

Run specific test suites:
```bash
cabal test plutus-core-test           # 15-25 minutes
cabal test untyped-plutus-core-test   # 10-15 minutes
cabal test plutus-ir-test             # 10-15 minutes
cabal test plutus-tx-test             # 10-15 minutes
cabal test plutus-ledger-api-test     # 5-10 minutes
```

### Golden Test Regeneration

Regenerate all golden test files:
```bash
./scripts/regen-goldens.sh  # NEVER CANCEL - takes 45-75 minutes, timeout: 120+ minutes
```

For plugin tests with multiple GHC versions:
```bash
nix develop .#ghc96 --command cabal test plutus-tx-plugin --test-options=--accept
```

### Validation Scenarios

ALWAYS run these validation steps after making changes:

1. **Build validation**:
   ```bash
   cabal build all --ghc-options=-Werror  # Must pass with no warnings
   ```

2. **Test validation**:
   ```bash
   cabal test all  # All tests must pass
   ```

3. **Specific functionality tests**:
   ```bash
   # Test Plutus Core evaluator
   cabal run plc evaluate -- --help
   
   # Test conformance (if modifying core evaluator)
   cabal run haskell-conformance -- --help
   cabal run agda-conformance -- --help
   
   # Test benchmarks (if modifying performance-critical code)
   cabal run plutus-benchmark-nofib-tests -- --help
   ```

4. **Formatting validation**:
   ```bash
   stylish-haskell --config .stylish-haskell.yaml --check <modified-files>
   cabal-fmt --check <modified-cabal-files>
   ```

### Performance and Conformance Testing

The repository includes specialized test suites:

**Conformance tests** (validate evaluator correctness):
- `plutus-conformance/` - Compare Haskell vs Agda implementations
- Run with: `cabal test haskell-conformance` and `cabal test agda-conformance`

**Benchmark tests** (validate performance):
- `plutus-benchmark/` - Performance regression tests
- Run with: `cabal test plutus-benchmark-nofib-tests`

## Development Tools and Linting

### Pre-commit Hooks and Formatting

Pre-commit hooks are defined in the Nix shell configuration and run automatically on commit. The Nix environment provides the following formatting tools:

```bash
# These tools are available in the Nix shell:
stylish-haskell --config .stylish-haskell.yaml <files>  # Haskell formatting
cabal-fmt <cabal-files>                                  # Cabal file formatting
fourmolu --mode inplace <files>                          # Alternative Haskell formatter
```

If you commit outside the Nix shell, you may get:
```
pre-commit not found. Did you forget to activate your virtualenv?
```

In this case, use `git commit --no-verify` or ensure you're in the Nix environment.

**CRITICAL:** Always run formatting before committing or CI will fail.

### Linting

Two hlint configurations exist:
- `./.hlint.yaml` - Suggested hints for editors
- `./.github/.hlint.yaml` - Enforced hints for CI

### Haskell Language Server

HLS is available in the Nix shell as `haskell-language-server` (not `haskell-language-server-wrapper`). Configure your editor to use this binary.

## Documentation Building

### Haddock Documentation

Build API documentation (60-90 minutes):
```bash
./scripts/combined-haddock.sh _haddock all  # NEVER CANCEL - takes 60-90 minutes, timeout: 120+ minutes
```

### Docusaurus Site

Navigate to documentation directory:
```bash
cd doc/docusaurus
```

Install dependencies and build (10-15 minutes):
```bash
yarn            # Install dependencies - 2-5 minutes
yarn build      # Build site - 5-10 minutes
yarn start      # Development server
```

## Package Structure and Key Locations

### Core Packages
- **plutus-core/** - Core language implementation and evaluator
- **plutus-tx/** - Plutus Tx compiler and libraries  
- **plutus-tx-plugin/** - GHC plugin for Plutus Tx compilation
- **plutus-ledger-api/** - Ledger integration APIs
- **plutus-metatheory/** - Agda mechanized metatheory (formal proofs)
- **plutus-executables/** - Command-line tools (plc, uplc, pir)
- **plutus-benchmark/** - Performance and regression tests
- **plutus-conformance/** - Evaluator correctness validation

### Agda Metatheory

The `plutus-metatheory/` package contains formal verification in Agda:
```bash
# Build the Agda evaluator
cabal build plutus-metatheory

# Run the Agda-based evaluator (equivalent to plc)
cabal run plc-agda -- --help

# Test conformance between Haskell and Agda implementations
cabal test plutus-metatheory
```

**Note:** When modifying `.lagda` files, regenerate Haskell modules with:
```bash
generate-malonzo-code  # Available in Nix shell
```

### Important Files
- **cabal.project** - Main project configuration
- **CONTRIBUTING.adoc** - Detailed contribution guidelines
- **scripts/** - Build and utility scripts
- **.github/workflows/** - CI/CD pipeline definitions

### Common Development Patterns

When modifying core functionality:
1. **Always check plutus-core/README.md** for package-specific guidance
2. **Update tests** in corresponding test/ directories  
3. **Regenerate golden files** if evaluator behavior changes
4. **Check multiple GHC versions** if touching plutus-tx-plugin

## CI Requirements

The CI pipeline requires:
1. **No compiler warnings** (builds with `-Werror`)
2. **All tests passing** across all supported GHC versions
3. **Proper formatting** (stylish-haskell, cabal-fmt)
4. **No lint violations** per `.github/.hlint.yaml`

## Troubleshooting Common Issues

### Build Failures
- **"package not found"** → Run `cabal update` in the Nix shell
- **Network issues with CHaP** → Ensure you're in proper Nix environment with `nix develop`
- **Missing dependencies** → Exit and re-enter `nix develop --no-warn-dirty --accept-flake-config`
- **"could not find module"** → Clean and rebuild: `cabal clean && cabal build all`

### Plugin Issues  
- **Cross-compilation problems** → Use GHC version conditionals in .cabal files
- **GHC version mismatch** → Use appropriate `nix develop .#ghc<version>` shell
- **"orphan instances" warnings** → Add `-Wno-orphans` to specific modules if safe

### Memory Issues During Build
- **OOM during compilation** → Add to cabal.project.local:
  ```
  package plutus-core
    ghc-options: -fexternal-interpreter
  ```
- **GHCi link errors with recursion-schemes** → Same fix as above

### Test Failures
- **Golden test mismatches** → Regenerate with `./scripts/regen-goldens.sh`
- **Conformance test failures** → Check if changes affect evaluator semantics
- **Plugin test failures** → Test with all supported GHC versions

### Environment Issues
- **HLS not working** → Ensure you're using `haskell-language-server` (not `-wrapper`)
- **Formatting errors in CI** → Run formatting tools before commit:
  ```bash
  stylish-haskell --config .stylish-haskell.yaml -i <files>
  cabal-fmt -i <cabal-files>
  ```

## Development Workflow Examples

### Adding a New Built-in Function
1. Modify `plutus-core/plutus-core/src/PlutusCore/Default/Builtins.hs`
2. Update cost model data in `plutus-core/cost-model/data/`
3. Regenerate golden tests: `./scripts/regen-goldens.sh` 
4. Test conformance: `cabal test haskell-conformance agda-conformance`
5. Run benchmarks: `cabal test plutus-benchmark-nofib-tests`

### Modifying the Evaluator
1. Make changes in `plutus-core/untyped-plutus-core/`
2. Update corresponding Agda code in `plutus-metatheory/src/`
3. Regenerate Haskell from Agda: `generate-malonzo-code`
4. Test conformance extensively: `cabal test plutus-metatheory`
5. Check performance impact: `cabal run plutus-benchmark`

### Working with Plutus Tx
1. Changes to `plutus-tx/` may require plugin updates in `plutus-tx-plugin/`
2. Test with multiple GHC versions:
   ```bash
   nix develop .#ghc96 --command cabal test plutus-tx-plugin
   ```
3. Update golden tests for all GHC versions if needed

## Essential Timing Reminders

**NEVER CANCEL ANY BUILD OR TEST COMMAND**

- Full builds: 45-90 minutes (timeout: 120+ minutes)
- All tests: 30-60 minutes (timeout: 90+ minutes) 
- Haddock generation: 60-90 minutes (timeout: 120+ minutes)
- Golden test regeneration: 45-75 minutes (timeout: 120+ minutes)

Always set appropriate timeouts and wait for completion. Cancelled builds waste time and may leave the environment in an inconsistent state.