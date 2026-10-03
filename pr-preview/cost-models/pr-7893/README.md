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

One page per builtin, one directory each. The list of pages lives in `PAGES`
in `shared/utils.js`, which also drives the navigation bar on every page.

## Project Structure

```text
doc/cost-models/
├── index.html              # Landing page with overview
├── shared/
│   ├── styles.css         # Shared CSS styling
│   └── utils.js           # Everything shared: page list (PAGES), navigation,
│                          # data-source panel and URL handling, CSV parser,
│                          # cost model evaluators, page bootstrap
│                          # (setupCostModelPage)
├── valuedata/
│   ├── index.html         # Page markup: heading, controls, info panel
│   └── plot.js            # Page identity and rendering only
├── unvaluedata/           # ... and so on, one directory per builtin
```

## Features

- **Interactive Plots**: 2D and 3D scatter plots with zoom, pan, and rotation
- **Model Overlay**: Compare benchmark data with fitted cost model predictions
- **Toggle Controls**: Show/hide model predictions and adjust axis ranges
- **Detailed Information**: View model formulas, parameters, overhead, and data ranges
- **Live Data**: Loads latest benchmark data from GitHub

## Data Sources

- **Benchmark Data**: `plutus-core/cost-model/data/benching-conway.csv`
- **Cost Models**: `plutus-core/cost-model/data/builtinCostModelE.json`

Data is loaded dynamically from the Plutus repository using the browser's `fetch()` API.

## Adding New Functions

### Quick Steps

1. Copy the directory of an existing function whose plot has the same shape:

   ```bash
   cp -r valuedata/ myfunction/
   ```

2. Add the page to `PAGES` in `shared/utils.js` (slug and display name).
   The navigation bar on every page and the landing page pick it up from
   there, so the pages that already exist stay untouched.

3. Edit `myfunction/plot.js`: the constants at the top (`FUNCTION_NAME` as it
   appears in the CSV, `COST_MODEL_NAME` as the key in the JSON, `ARITY`), the
   `slug` in the `setupCostModelPage` call, and the rendering functions.
   Loading, URL handling and navigation come from `setupCostModelPage`.

4. Edit `myfunction/index.html`: page title, heading, description, and the
   info panel labels.

5. If the function's cost model type has no entry in `CostModelEvaluators` in
   `shared/utils.js`, add one there and a matching case in
   `formatModelFormula`. Take the coefficient names from the JSON file, not
   from other evaluators; a name mismatch silently evaluates the model as
   zero.

6. Test locally:

   ```bash
   python -m http.server 8000
   # Visit http://localhost:8000/myfunction/
   ```

### Page Skeleton

```javascript
const FUNCTION_NAME = 'MyFunction';    // CSV uses PascalCase
const COST_MODEL_NAME = 'myFunction';  // JSON uses camelCase
const ARITY = 2;

setupCostModelPage({
  slug: 'myfunction',
  functionName: FUNCTION_NAME,
  costModelName: COST_MODEL_NAME,
  arity: ARITY,
  render(data) {
    // Draw the plots from data.benchmarkData, data.costModel,
    // data.overhead, data.modelPredictions.
  },
  setupControls() {
    // Wire page-specific controls (checkboxes, selectors).
  }
});
```

## Technical Details

### Architecture

- Plain HTML/CSS/JavaScript (no build tools)
- Plotly.js for interactive plotting
- Modern browser support only
- Desktop-focused design

### Cost Model Evaluation

`CostModelEvaluators` in `shared/utils.js` implements one evaluator per cost
model type, keyed by the `type` string from the JSON file. The coefficient
names inside each evaluator must match the JSON's `arguments` keys exactly.

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

- Verify function name matches key in `builtinCostModelE.json`
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
