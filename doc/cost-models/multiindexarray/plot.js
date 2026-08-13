// MultiIndexArray plot configuration and rendering
//
// Benchmark names are MultiIndexArray/<arraySize>/<indexCount>, so
// args[0] = array size and args[1] = index count.  The
// cost model is quadratic_in_y: it depends on the number of indices and not on
// the array size.
//
// The main view is a 3D scatter (array size, index count, time) with the
// fitted model drawn as a surface: flat along the array-size axis, rising
// along the index-count axis.  A histogram of net per-index times at large index counts
// makes the distribution of the benchmark results (and any multi-modality)
// directly visible.

// Configuration
const FUNCTION_NAME = 'MultiIndexArray';  // CSV uses PascalCase
const COST_MODEL_NAME = 'multiIndexArray';  // JSON uses camelCase
const ARITY = 2;

// Global state
let benchmarkData = [];
let modelPredictions = [];
let costModel = null;
let overhead = 0;
let showModel = true;
let zAxisMode = 'zero';
let histThreshold = 500;

setupCostModelPage({
  slug: 'multiindexarray',
  functionName: FUNCTION_NAME,
  costModelName: COST_MODEL_NAME,
  arity: ARITY,
  render(data) {
    ({ benchmarkData, costModel, overhead, modelPredictions } = data);
    updateInfoPanel();
    renderPlot();
    renderHistogram();
  },
  setupControls
});

function updateInfoPanel() {
  // Calculate stats over the index count (second argument)
  const stats = calculateStats(benchmarkData, 1);

  // Update data points
  document.getElementById('info-data-points').textContent = stats.dataPoints;

  // Update ranges
  if (stats.minArg !== undefined) {
    document.getElementById('info-x-range').textContent = `${stats.minArg} - ${stats.maxArg}`;
  }

  const arraySizes = benchmarkData.map(d => d.args[0]);
  document.getElementById('info-array-range').textContent =
    `${Math.min(...arraySizes)} - ${Math.max(...arraySizes)}`;

  document.getElementById('info-time-range').textContent = stats.timeRange;

  // Update model info
  if (costModel) {
    document.getElementById('info-model-type').textContent = costModel.modelType;
    document.getElementById('info-model-formula').textContent = formatModelFormula(
      costModel.modelType,
      costModel.coefficients
    );
  } else {
    document.getElementById('info-model-type').textContent = 'Not available';
    document.getElementById('info-model-formula').textContent = 'Cost model not found';
  }

  // Update overhead
  if (overhead > 0) {
    document.getElementById('info-overhead').textContent =
      `${overhead.toFixed(2)} ns (arity ${ARITY}) added to predictions`;
  } else {
    document.getElementById('info-overhead').textContent = 'Not calculated';
  }
}

// The model surface: the fitted cost at each index count (+ overhead), flat
// along the array-size axis.
function modelPlaneTrace() {
  const arraySizes = [...new Set(benchmarkData.map(d => d.args[0]))].sort((a, b) => a - b);
  const maxIndexCount = Math.max(...benchmarkData.map(d => d.args[1]));
  const steps = 30;
  const indexCounts = Array.from({ length: steps + 1 }, (_, i) => Math.max(1, Math.round(i * maxIndexCount / steps)));

  const evaluate = CostModelEvaluators[costModel.modelType];

  // z[i][j] corresponds to (y = indexCounts[i], x = arraySizes[j])
  const z = indexCounts.map(n =>
    arraySizes.map(h => evaluate(costModel.coefficients, [h, n]) / 1000 + overhead));

  return {
    x: arraySizes,
    y: indexCounts,
    z: z,
    type: 'surface',
    name: 'Model Prediction',
    showscale: false,
    opacity: 0.35,
    colorscale: [[0, '#E53E3E'], [1, '#E53E3E']],
    hovertemplate: 'indices: %{y}<br>model: %{z:.0f} ns<extra></extra>'
  };
}

function renderPlot() {
  const benchmarkTrace = {
    x: benchmarkData.map(d => d.args[0]),
    y: benchmarkData.map(d => d.args[1]),
    z: benchmarkData.map(d => d.time),
    mode: 'markers',
    type: 'scatter3d',
    name: 'Benchmark Data',
    hovertemplate: 'array: %{x}<br>indices: %{y}<br>time: %{z:.0f} ns<extra></extra>',
    marker: {
      size: 3.5,
      color: '#0033AD',
      opacity: 0.75
    }
  };

  const traces = [benchmarkTrace];

  if (showModel && costModel && CostModelEvaluators[costModel.modelType]) {
    traces.push(modelPlaneTrace());
  } else if (showModel && modelPredictions.length > 0) {
    // Fallback for other model shapes: prediction markers at the data points
    traces.push({
      x: modelPredictions.map(d => d.args[0]),
      y: modelPredictions.map(d => d.args[1]),
      z: modelPredictions.map(d => d.predictedTime),
      mode: 'markers',
      type: 'scatter3d',
      name: 'Model Predictions',
      marker: { size: 3.5, color: '#E53E3E', opacity: 0.4, symbol: 'x' }
    });
  }

  const benchmarkZ = benchmarkTrace.z;

  // Layout configuration
  const layout = {
    title: {
      text: `${FUNCTION_NAME} - Benchmark vs Model (3D)`,
      font: { size: 20 }
    },
    scene: {
      xaxis: {
        title: 'Array size (log)',
        type: 'log',
        gridcolor: '#E0E0E0'
      },
      yaxis: {
        title: 'Index count',
        gridcolor: '#E0E0E0'
      },
      zaxis: {
        title: 'Time (nanoseconds)',
        gridcolor: '#E0E0E0'
      },
      camera: {
        eye: { x: 1.7, y: -1.7, z: 0.6 }
      }
    },
    showlegend: true,
    legend: {
      x: 0.02,
      y: 0.98,
      bgcolor: 'rgba(255, 255, 255, 0.8)',
      bordercolor: '#BDC3C7',
      borderwidth: 1
    },
    paper_bgcolor: 'rgba(0,0,0,0)'
  };

  // Set Z-axis range based on mode
  if (zAxisMode === 'zero') {
    layout.scene.zaxis.range = [0, Math.max(...benchmarkZ) * 1.1];
  } else {
    const minZ = Math.min(...benchmarkZ);
    const maxZ = Math.max(...benchmarkZ);
    const padding = (maxZ - minZ) * 0.1;
    layout.scene.zaxis.range = [minZ - padding, maxZ + padding];
  }

  // Config
  const config = {
    responsive: true,
    displayModeBar: true,
    displaylogo: false
  };

  // Render
  const container = document.getElementById('plot-container');
  container.innerHTML = '';
  Plotly.newPlot('plot-container', traces, layout, config);
}

function renderHistogram() {
  const container = document.getElementById('hist-container');

  // Net per-index time for large index counts
  const points = benchmarkData.filter(d => d.args[1] >= histThreshold);
  if (points.length === 0) {
    container.innerHTML = `<div class="error"><p>No benchmarks with index count ≥ ${histThreshold}</p></div>`;
    return;
  }

  const perIndex = points.map(d => (d.time - overhead) / d.args[1]);

  const histTrace = {
    x: perIndex,
    type: 'histogram',
    name: `per-index time (y ≥ ${histThreshold})`,
    xbins: { size: 1 },
    marker: {
      color: '#0033AD',
      opacity: 0.8
    }
  };

  const layout = {
    title: {
      text: `Distribution of net per-index time (index count ≥ ${histThreshold}, n = ${points.length})`,
      font: { size: 18 }
    },
    xaxis: {
      title: 'Net time per index (nanoseconds)',
      gridcolor: '#E0E0E0'
    },
    yaxis: {
      title: 'Benchmark count',
      gridcolor: '#E0E0E0'
    },
    bargap: 0.05,
    plot_bgcolor: '#FAFAFA',
    paper_bgcolor: 'rgba(0,0,0,0)',
    shapes: [],
    annotations: []
  };

  // Mark the model's net time per index (ps -> ns) at the histogram threshold on
  // the distribution.  The model is not linear in the index count, so this is the
  // average over the indices of one call rather than a single slope.
  const evaluate = costModel && CostModelEvaluators[costModel.modelType];
  if (evaluate && histThreshold > 0) {
    const coeffs = costModel.coefficients;
    const perIndexNs =
      (evaluate(coeffs, [0, histThreshold]) - evaluate(coeffs, [0, 0])) / histThreshold / 1000;
    layout.shapes.push({
      type: 'line',
      x0: perIndexNs, x1: perIndexNs,
      y0: 0, y1: 1,
      yref: 'paper',
      line: { color: '#E53E3E', width: 2, dash: 'dash' }
    });
    layout.annotations.push({
      x: perIndexNs,
      y: 1,
      yref: 'paper',
      yanchor: 'bottom',
      text: `model: ${perIndexNs.toFixed(1)} ns/index at ${histThreshold}`,
      showarrow: false,
      font: { color: '#E53E3E' }
    });
  }

  const config = {
    responsive: true,
    displayModeBar: true,
    displaylogo: false
  };

  container.innerHTML = '';
  Plotly.newPlot('hist-container', [histTrace], layout, config);
}

function setupControls() {
  // Show/hide model checkbox
  const showModelCheckbox = document.getElementById('show-model');
  showModelCheckbox.addEventListener('change', (e) => {
    showModel = e.target.checked;
    renderPlot();
  });

  // Z-axis mode selector
  const zAxisModeSelect = document.getElementById('z-axis-mode');
  zAxisModeSelect.addEventListener('change', (e) => {
    zAxisMode = e.target.value;
    renderPlot();
  });

  // Histogram threshold selector
  const histThresholdSelect = document.getElementById('hist-threshold');
  histThresholdSelect.addEventListener('change', (e) => {
    histThreshold = parseInt(e.target.value, 10);
    renderHistogram();
  });
}
