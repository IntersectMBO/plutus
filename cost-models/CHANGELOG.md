# Changelog

## 2025-11-14 - Initial Implementation

### Created

- Complete static website for visualizing Plutus Core builtin cost models
- Four function visualizations: ValueData, UnValueData, ValueContains, LookupCoin
- Shared utilities for CSV parsing, cost model evaluation, and overhead calculation
- Scientific/academic styling with Cardano brand colors
- Interactive 2D and 3D Plotly visualizations

### Data Format Fixes

- **CSV Parser**: Updated to handle actual benching-conway.csv format
  - CSV has header row: `benchmark,t,t.mean.lb,t.mean.ub,t.sd,t.sd.lb,t.sd.ub`
  - Uses 't' column (mean execution time in seconds)
  - Converts seconds to nanoseconds for display
  - Skips header and comment lines (starting with #)

- **Function Names**: CSV uses PascalCase, JSON uses camelCase
  - CSV: `ValueData`, `UnValueData`, `ValueContains`, `LookupCoin`
  - JSON: `valueData`, `unValueData`, `valueContains`, `lookupCoin`

- **Cost Model Structure**: Updated to handle actual JSON format
  - For `constant_cost`: `arguments` is a single number (e.g., 159159)
  - For other models: `arguments` is an object with `intercept` and `slope` keys
  - Not `c0`/`c1`/`c2` as originally assumed

- **Coefficient Naming**: Support both naming conventions
  - Original: `c0`, `c1`, `c2`
  - Actual: `intercept`, `slope`
  - Code now handles both for maximum compatibility

### Model Types Implemented

- `constant_cost`
- `linear_in_x`, `linear_in_y`, `linear_in_z`
- `quadratic_in_x`, `quadratic_in_y`, `quadratic_in_z`
- `linear_in_xy`, `linear_in_xz`, `linear_in_yz`
- `addedSizes`
- `multipliedSizes` / `multiplied_sizes` (both snake_case and camelCase)
- `minSize`, `maxSize`
- `linear_in_max_yz`

### Features

- **Interactive Controls**:
  - Toggle model predictions on/off
  - Switch Y-axis (2D) or Z-axis (3D) between "start from 0" and "auto-scale"
  - Standard Plotly controls (zoom, pan, rotate)

- **Information Panels**:
  - Cost model type and formula
  - Overhead calculation (per-arity, from Nop benchmarks)
  - Data point statistics
  - Argument ranges and time ranges
  - Links to GitHub data sources

- **Template-Based Architecture**:
  - Easy to add new functions by copying existing directories
  - Clear separation of shared utilities and function-specific code
  - Comprehensive documentation in README and landing page

### Known Limitations

- Desktop-only design (no mobile responsive)
- Modern browsers only (no legacy support)
- Loads data from GitHub (requires internet connection)
- CORS may be an issue depending on browser settings

### Testing

Tested with local HTTP server:
```bash
python3 -m http.server 8000
```

All four visualizations load correctly and display data from actual CSV and JSON files.
