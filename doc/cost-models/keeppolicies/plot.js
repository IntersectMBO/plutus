// KeepPolicies plot configuration and rendering (3D)

const FUNCTION_NAME = 'KeepPolicies'; // CSV uses PascalCase
const COST_MODEL_NAME = 'keepPolicies'; // JSON uses camelCase
const ARITY = 2;

let benchmarkData = [];
let costModel = null;
let stockModel = null;
let overhead = 0;
let showModel = true;
let axisScale = 'log';

setupCostModelPage({
  slug: 'keeppolicies',
  functionName: FUNCTION_NAME,
  costModelName: COST_MODEL_NAME,
  arity: ARITY,
  render(data) {
    ({ benchmarkData, costModel, overhead } = data);
    // The plain `lm(t ~ x_mem + y_mem)` of models.R, refit in the browser on the same
    // points the shipped fit was built from. The shipped model comes from that same fit
    // (negative coefficients clamped), so the two blocks agreeing checks that the JSON
    // matches the fit; the undercharge lines show where the plane sits below the data.
    stockModel = fitLinearInXAndY(benchmarkData.filter(d => d.args[1] > 0), overhead);
    updateInfoPanel();
    renderPlot();
  },
  setupControls
});

function updateInfoPanel() {
  const stats = calculateStats(benchmarkData);
  document.getElementById('info-data-points').textContent = stats.dataPoints;

  const xs = benchmarkData.map(d => d.args[0]);
  const ys = benchmarkData.map(d => d.args[1]);
  document.getElementById('info-x-range').textContent =
    `${Math.min(...xs)} - ${Math.max(...xs)}`;
  document.getElementById('info-y-range').textContent =
    `${Math.min(...ys)} - ${Math.max(...ys)}`;
  document.getElementById('info-time-range').textContent = stats.timeRange;
  document.getElementById('info-overhead').textContent = overhead > 0
    ? `${overhead.toFixed(2)} ns (arity ${ARITY}) added to predictions`
    : 'Not calculated';

  // Summarize both fits over the population they were built on (the y = 0 controls are
  // out of the fit, so they would only distort the undercharge and overcharge lines).
  const fitted = benchmarkData.filter(d => d.args[1] > 0);
  document.getElementById('fit-comparison').innerHTML =
    fitSummary('The shipped model (from the cost-model JSON)',
               costModel, fitted, overhead, ['p', 'n'])
    + fitSummary('The same least-squares fit recomputed from the CSV',
                 stockModel, fitted, overhead, ['p', 'n']);

  if (costModel) {
    document.getElementById('info-model-type').textContent = costModel.modelType;
    document.getElementById('info-model-formula').textContent =
      formatModelFormula(costModel.modelType, costModel.coefficients);
  } else {
    document.getElementById('info-model-type').textContent = 'Not available';
    document.getElementById('info-model-formula').textContent = 'Cost model not found';
  }
}

/* The two argument sizes on the floor, time up. Every benchmark point appears twice at the
same place on the floor, once as what it measured and once as what the model charges for it,
so the model is safe exactly where the red crosses sit above the blue dots. The sizes are
sampled log-uniformly, so a log floor is what spreads them out; the cost of that is the few
points at p = 0 or n = 0, which a log axis cannot place and which are out of the fit anyway. */
function plotTraces() {
  const traces = [{
    x: benchmarkData.map(d => d.args[0]),
    y: benchmarkData.map(d => d.args[1]),
    z: benchmarkData.map(d => d.time),
    mode: 'markers',
    type: 'scatter3d',
    name: 'Benchmark Data',
    marker: { size: 4, color: '#0033AD', opacity: 0.8 },
    hovertemplate: 'p %{x}, n %{y}<br>measured %{z:.3s} ns<extra></extra>'
  }];

  if (showModel && costModel) {
    traces.push({
      x: benchmarkData.map(d => d.args[0]),
      y: benchmarkData.map(d => d.args[1]),
      z: benchmarkData.map(d => modelCharge(costModel, d.args, overhead)),
      mode: 'markers',
      type: 'scatter3d',
      name: 'Model Predictions',
      marker: { size: 4, color: '#E53E3E', opacity: 0.6, symbol: 'x' },
      hovertemplate: 'p %{x}, n %{y}<br>charged %{z:.3s} ns<extra></extra>'
    });
  }
  return traces;
}

const PLOT_CONFIG = { responsive: true, displayModeBar: true, displaylogo: false };

function renderPlot() {
  ensurePlotPanel('plot-3d');
  const scaled = axisScale;
  const suffix = axisScale === 'log' ? ', log' : '';
  Plotly.react('plot-3d', plotTraces(), {
    title: { text: `${FUNCTION_NAME} - Benchmark vs Model (3D)`, font: { size: 20 } },
    scene: {
      xaxis: { title: `Policy list length (p${suffix})`, gridcolor: '#E0E0E0', type: scaled },
      yaxis: { title: `Value total size (n${suffix})`, gridcolor: '#E0E0E0', type: scaled },
      zaxis: { title: `Time (ns${suffix})`, gridcolor: '#E0E0E0', type: scaled },
      camera: { eye: { x: 1.7, y: -1.7, z: 0.7 } }
    },
    showlegend: true,
    legend: {
      x: 0.02,
      y: 0.98,
      bgcolor: 'rgba(255, 255, 255, 0.8)',
      bordercolor: '#BDC3C7',
      borderwidth: 1
    },
    margin: { t: 60, b: 10, l: 10, r: 10 },
    height: 700,
    paper_bgcolor: 'rgba(0,0,0,0)'
  }, PLOT_CONFIG);
}

function setupControls() {
  document.getElementById('show-model').addEventListener('change', e => {
    showModel = e.target.checked;
    renderPlot();
  });
  document.getElementById('axis-scale').addEventListener('change', e => {
    axisScale = e.target.value;
    renderPlot();
  });
}
