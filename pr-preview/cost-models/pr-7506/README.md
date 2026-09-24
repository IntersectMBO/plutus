# Plutus Cost Model Visualization

Interactive visualizations of Plutus Core builtin function cost models using Plotly.js.

## Quick Start

### Local Development

Start a local HTTP server in this directory:

```bash
python -m http.server 8000
# or
python3 -m http.server 8000
```

Then open your browser to:

- <http://localhost:8000/>

### Available Visualizations

- **ValueData** - Converts Value to Data representation (2D plot)
- **UnValueData** - Converts Data back to Value (2D plot)
- **ValueContains** - Checks if one Value contains another (3D plot)
- **LookupCoin** - Looks up a coin in a Value (2D plot)

## Project Structure

```text
doc/cost-models/
├── index.html              # Landing page with overview
├── shared/
│   ├── styles.css         # Shared CSS styling
│   └── utils.js           # Shared utilities (CSV parser, cost model evaluator)
├── valuedata/
│   ├── index.html         # ValueData visualization page
│   └── plot.js            # ValueData-specific plot configuration
├── unvaluedata/
│   ├── index.html
│   └── plot.js
├── valuecontains/
│   ├── index.html
│   └── plot.js
└── lookupcoin/
    ├── index.html
    └── plot.js
```

## Features

- **Interactive Plots**: 2D and 3D scatter plots with zoom, pan, and rotation
- **Model Overlay**: Compare benchmark data with fitted cost model predictions
- **Toggle Controls**: Show/hide model predictions and adjust axis ranges
- **Detailed Information**: View model formulas, parameters, overhead, and data ranges
- **Live Data**: Loads latest benchmark data from GitHub

## Data Sources

- **Benchmark Data**: `plutus-core/cost-model/data/benching-conway.csv`
- **Cost Models**: `plutus-core/cost-model/data/builtinCostModelC.json`

Data is loaded dynamically from the Plutus repository using the browser's `fetch()` API.

## Adding New Functions

### Quick Steps

1. Copy an existing function directory:

   ```bash
   cp -r valuedata/ myfunction/
   ```

2. Edit `myfunction/index.html`:
   - Update page title and heading
   - Update navigation links
   - Update plot information panel labels

3. Edit `myfunction/plot.js`:
   - Update `FUNCTION_NAME` constant (must match CSV entry)
   - Update `ARITY` constant (number of arguments)
   - Adjust plot type if needed (2D vs 3D)
   - Update axis labels

4. Test locally:

   ```bash
   python -m http.server 8000
   # Visit http://localhost:8000/myfunction/
   ```

5. Add to navigation:
   - Update `index.html` to include your function
   - Add navigation link to all other function pages

### Configuration Examples

**2D plot with one argument:**

```javascript
const FUNCTION_NAME = 'MyFunction';
const ARITY = 1;

const benchmarkX = benchmarkData.map(d => d.args[0]);
const benchmarkY = benchmarkData.map(d => d.time);
```

**3D plot with two arguments:**

```javascript
const FUNCTION_NAME = 'MyFunction';
const ARITY = 2;

const benchmarkX = benchmarkData.map(d => d.args[0]);
const benchmarkY = benchmarkData.map(d => d.args[1]);
const benchmarkZ = benchmarkData.map(d => d.time);
```

## Technical Details

### Architecture

- Plain HTML/CSS/JavaScript (no build tools)
- Plotly.js for interactive plotting
- Modern browser support only
- Desktop-focused design

### Cost Model Evaluation

JavaScript implementations of cost model evaluators:

- `constant_cost`
- `linear_in_x`, `linear_in_y`, `linear_in_z`
- `quadratic_in_x`, `quadratic_in_y`, `quadratic_in_z`
- `linear_in_xy`, `linear_in_xz`, `linear_in_yz`
- `addedSizes`, `multipliedSizes`
- `minSize`, `maxSize`
- `linear_in_max_yz`

### Overhead Calculation

Overhead is automatically calculated from `Nop` benchmarks in the CSV file and added to all model predictions.

## Deployment

The site is automatically deployed to GitHub Pages via CI/CD:

- **Production**: https://plutus.cardano.intersectmbo.org/cost-models/
- **Workflow**: `.github/workflows/cost-models-site.yml`
- **Triggers**: Push to `master` or manual dispatch
- **PR Previews**: Automatically deployed for pull requests

No build process required - the workflow copies static files directly to `gh-pages`.

## Troubleshooting

**Data not loading:**

- Check browser console for CORS errors
- Verify CSV path matches exactly (case-sensitive)
- Try loading the CSV URL directly in your browser

**Model not found:**

- Verify function name matches key in `builtinCostModelC.json`
- Check console for detailed error messages

**Plot not rendering:**

- Check Plotly errors in console
- Verify data structure and axis mappings
- Ensure Plotly.js loaded correctly

**Unsupported model type:**

- Check console for model type name
- Add new evaluator in `shared/utils.js` if needed

## Browser Compatibility

Requires modern browsers:

- Chrome/Edge (latest)
- Firefox (latest)
- Safari (latest)

No legacy browser support needed for this technical audience.

## Links

- [Plutus Repository](https://github.com/IntersectMBO/plutus)
- [Plutus Documentation](https://plutus.cardano.intersectmbo.org/docs/)
- [Plotly.js Documentation](https://plotly.com/javascript/)
