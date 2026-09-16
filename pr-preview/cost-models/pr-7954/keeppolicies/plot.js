// KeepPolicies plot configuration and rendering (3D)

const FUNCTION_NAME = 'KeepPolicies'; // CSV uses PascalCase
const COST_MODEL_NAME = 'keepPolicies'; // JSON uses camelCase
const ARITY = 2;

let benchmarkData = [];
let shippedModel = null;
let costModel = null; // the shipped model, or the coefficients typed into the info panel
let overhead = 0;
let axisScale = 'linear';

setupCostModelPage({
  slug: 'keeppolicies',
  functionName: FUNCTION_NAME,
  costModelName: COST_MODEL_NAME,
  arity: ARITY,
  render(data) {
    ({ benchmarkData, costModel, overhead } = data);
    shippedModel = costModel;
    updateInfoPanel();
    renderPlot();
    renderCoefficientEditor(shippedModel, model => {
      costModel = model;
      updateInfoPanel();
      renderPlot();
    });
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
    ? `${overhead.toFixed(2)} ns (arity ${ARITY})`
    : 'Not calculated';

  // Every point is in the fit. The empty `Value` has an outer-map depth of 1 rather than
  // 0, so the points that measure the policy list on its own sit on the bottom edge of the
  // plane instead of off it, and they are what pins the term proportional to the list.
  renderFitSummary(costModel, shippedModel, benchmarkData, overhead, ['p', 'L']);

  if (costModel) {
    document.getElementById('info-model-type').textContent = costModel.modelType;
    document.getElementById('info-model-formula').textContent =
      formatModelFormula(costModel.modelType, costModel.coefficients);
  } else {
    document.getElementById('info-model-type').textContent = 'Not available';
    document.getElementById('info-model-formula').textContent = 'Cost model not found';
  }
}

/* The two argument sizes are the horizontal axes and time the vertical one. Every benchmark
point is drawn twice at the same list length and depth, once as what it measured and once as
what the model charges for it, so the model is safe exactly where the red crosses sit above
the blue dots. The model can instead be drawn as a translucent surface over the whole plane,
which shows its shape where the sample is thin. Linear axes are the default: the bound on
the number of policies makes the domain finite, and the linear grid in the benchmark fills it
evenly, so the whole plane is visible at once and the point at p = 0 has a place. Log axes
spread out the log-uniform part of the sample at the small end, at the cost of that point.
The depth axis is already logarithmic in the size of the `Value`, so it stays linear. */
function plotTraces() {
  const traces = [{
    x: benchmarkData.map(d => d.args[0]),
    y: benchmarkData.map(d => d.args[1]),
    z: benchmarkData.map(d => d.time),
    mode: 'markers',
    type: 'scatter3d',
    name: 'Benchmark Data',
    marker: { size: 4, color: '#0033AD', opacity: 0.8 },
    hovertemplate: 'p %{x}, L %{y}<br>measured %{z:.3s} ns<extra></extra>'
  }];

  const modelTrace = modelTrace3d(costModel, benchmarkData, overhead, {
    xLog: axisScale === 'log',
    hover: 'p %{x}, L %{y}<br>charged %{z:.3s} ns<extra></extra>'
  });
  if (modelTrace) traces.push(modelTrace);
  return traces;
}

const PLOT_CONFIG = { responsive: true, displayModeBar: true, displaylogo: false };

function renderPlot() {
  ensurePlotPanel('plot-3d');
  const scaled = axisScale;
  const suffix = axisScale === 'log' ? ', log' : '';
  Plotly.react('plot-3d', plotTraces(), {
    // A constant `uirevision` keeps the camera the reader has rotated to across re-renders;
    // without it every control change snaps the view back to the initial eye, which reads
    // as the data having flipped.
    uirevision: FUNCTION_NAME,
    title: { text: `${FUNCTION_NAME} - Benchmark vs Model (3D)`, font: { size: 20 } },
    scene: {
      xaxis: { title: `Policy list length (p${suffix})`, gridcolor: '#E0E0E0', type: scaled },
      yaxis: { title: 'Value outer map depth (L)', gridcolor: '#E0E0E0', type: 'linear' },
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
  setupModelDisplay(renderPlot);
  document.querySelectorAll('input[name="axis-scale"]').forEach(r =>
    r.addEventListener('change', e => {
      axisScale = e.target.value;
      renderPlot();
    }));
}
