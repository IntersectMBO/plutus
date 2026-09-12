// MultiIndexArray plot configuration and rendering
//
// Benchmark names are MultiIndexArray/<arraySize>/<indexCount>, so
// args[0] = array size and args[1] = index count.  The
// cost model is quadratic_in_y: it depends on the number of indices and not on
// the array size.
//
// The main view is a 2D scatter of time against index count, with one colour
// per array size and the fitted model drawn as a line.  The array-size
// independence the model assumes shows up directly: points of every colour lie
// on the same curve.  A second panel plots the per-index cost with the model's
// per-call constant subtracted, which is the view where its rise across the
// range is visible.  A histogram of the same per-index costs at large index
// counts makes their distribution (and any multi-modality) directly visible.

// Configuration
const FUNCTION_NAME = 'MultiIndexArray';  // CSV uses PascalCase
const COST_MODEL_NAME = 'multiIndexArray';  // JSON uses camelCase
const ARITY = 2;

// The benchmark's random points use array sizes at every power of two, so
// colouring by exact size would need a colour per size.  Bucket the sizes
// instead, one ordered dark-to-warm colour per bucket (upper bounds,
// inclusive).
const ARRAY_SIZE_BUCKETS = [
  { limit: 8, color: '#0D0887' },
  { limit: 64, color: '#6A00A8' },
  { limit: 512, color: '#B12A90' },
  { limit: 4096, color: '#D6556D' },
  { limit: 32768, color: '#EF7E50' },
  { limit: Infinity, color: '#FCA636' }
];

// Below this index count the per-call constant dominates the total, and
// dividing the small remainder by the count amplifies noise.
const PER_INDEX_MIN_COUNT = 50;

// Global state
let benchmarkData = [];
let modelPredictions = [];
let costModel = null;
let overhead = 0;
let showModel = true;
let yAxisMode = 'zero';
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
    renderPerIndex();
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

// The model evaluated at index count n, in nanoseconds, overhead included.
function modelAt(n) {
  const evaluate = CostModelEvaluators[costModel.modelType];
  return evaluate(costModel.coefficients, [0, n]) / 1000 + overhead;
}

// The model's per-call constant, in nanoseconds, without overhead.
function modelConstant() {
  const evaluate = CostModelEvaluators[costModel.modelType];
  return evaluate(costModel.coefficients, [0, 0]) / 1000;
}

// One scatter trace per array-size bucket, so the legend doubles as a size key
// and single buckets can be toggled to check that no colour sits apart from
// the rest.  The hover still reports the exact array size of each point.
function perSizeTraces(pointsToXY) {
  let lower = 1;
  return ARRAY_SIZE_BUCKETS.flatMap(bucket => {
    const from = lower;
    lower = bucket.limit + 1;
    const inBucket = benchmarkData.filter(d => from <= d.args[0] && d.args[0] <= bucket.limit);
    const points = inBucket.map(d => {
      const xy = pointsToXY(d);
      return xy && { ...xy, size: d.args[0] };
    }).filter(Boolean);
    if (points.length === 0) return [];
    const name = bucket.limit === Infinity
      ? `array size > ${from - 1}`
      : from === bucket.limit ? `array size ${from}` : `array size ${from}-${bucket.limit}`;
    return [{
      x: points.map(p => p.x),
      y: points.map(p => p.y),
      customdata: points.map(p => p.size),
      mode: 'markers',
      type: 'scatter',
      name,
      hovertemplate: 'array: %{customdata}<br>indices: %{x}<br>%{y:.1f} ns<extra></extra>',
      marker: {
        size: 6,
        color: bucket.color,
        opacity: 0.75
      }
    }];
  });
}

// Index counts at which to draw the model line.
function modelLineCounts() {
  const maxIndexCount = Math.max(...benchmarkData.map(d => d.args[1]));
  const steps = 64;
  return Array.from({ length: steps + 1 }, (_, i) =>
    Math.max(1, Math.round(i * maxIndexCount / steps)));
}

function renderPlot() {
  const traces = perSizeTraces(d => ({ x: d.args[1], y: d.time }));

  const haveEvaluator = costModel && CostModelEvaluators[costModel.modelType];
  if (showModel && haveEvaluator) {
    const counts = modelLineCounts();
    traces.push({
      x: counts,
      y: counts.map(modelAt),
      mode: 'lines',
      type: 'scatter',
      name: 'Model',
      line: { color: '#E53E3E', width: 2 },
      hovertemplate: 'indices: %{x}<br>model: %{y:.0f} ns<extra></extra>'
    });
  } else if (showModel && modelPredictions.length > 0) {
    // Fallback for other model shapes: prediction markers at the data points
    traces.push({
      x: modelPredictions.map(d => d.args[1]),
      y: modelPredictions.map(d => d.predictedTime),
      mode: 'markers',
      type: 'scatter',
      name: 'Model Predictions',
      marker: { size: 6, color: '#E53E3E', opacity: 0.4, symbol: 'x' }
    });
  }

  const benchmarkTimes = benchmarkData.map(d => d.time);

  // Layout configuration
  const layout = {
    title: {
      text: `${FUNCTION_NAME} - Benchmark vs Model`,
      font: { size: 20 }
    },
    xaxis: {
      title: 'Index count',
      gridcolor: '#E0E0E0'
    },
    yaxis: {
      title: 'Time (nanoseconds)',
      gridcolor: '#E0E0E0'
    },
    hovermode: 'closest',
    showlegend: true,
    legend: {
      x: 0.02,
      y: 0.98,
      bgcolor: 'rgba(255, 255, 255, 0.8)',
      bordercolor: '#BDC3C7',
      borderwidth: 1
    },
    plot_bgcolor: '#FAFAFA',
    paper_bgcolor: 'rgba(0,0,0,0)'
  };

  // Set Y-axis range based on mode
  if (yAxisMode === 'zero') {
    layout.yaxis.range = [0, Math.max(...benchmarkTimes) * 1.1];
  } else {
    const minY = Math.min(...benchmarkTimes);
    const maxY = Math.max(...benchmarkTimes);
    const padding = (maxY - minY) * 0.1;
    layout.yaxis.range = [minY - padding, maxY + padding];
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

// Per-index cost with the per-call constant subtracted:
// (t - overhead - c0) / indexCount against the index count.  The model's
// charge per index is then c1 + c2*y, a straight line, and the rise of the
// measured per-index cost across the range is visible instead of being
// swamped by the constant.
function renderPerIndex() {
  const container = document.getElementById('perindex-container');

  if (!(costModel && CostModelEvaluators[costModel.modelType])) {
    container.innerHTML =
      '<div class="error"><p>Per-index view needs an evaluable cost model</p></div>';
    return;
  }

  const c0 = modelConstant();
  const traces = perSizeTraces(d =>
    d.args[1] >= PER_INDEX_MIN_COUNT
      ? { x: d.args[1], y: (d.time - overhead - c0) / d.args[1] }
      : null);

  if (showModel) {
    const counts = modelLineCounts().filter(n => n >= PER_INDEX_MIN_COUNT);
    traces.push({
      x: counts,
      y: counts.map(n => (modelAt(n) - overhead - c0) / n),
      mode: 'lines',
      type: 'scatter',
      name: 'Model',
      line: { color: '#E53E3E', width: 2 },
      hovertemplate: 'indices: %{x}<br>model: %{y:.2f} ns/index<extra></extra>'
    });
  }

  const layout = {
    title: {
      text: `Per-index cost across the range (index count ≥ ${PER_INDEX_MIN_COUNT})`,
      font: { size: 18 }
    },
    xaxis: {
      title: 'Index count',
      gridcolor: '#E0E0E0'
    },
    // Auto-scaled on purpose: the rise across the range is the point of this
    // panel, and from zero it flattens into invisibility.
    yaxis: {
      title: 'Net time per index (nanoseconds)',
      gridcolor: '#E0E0E0'
    },
    hovermode: 'closest',
    showlegend: true,
    // Below the axis: anywhere inside the plot area it covers data, because
    // the auto-scaled panel has points in every corner.
    legend: {
      orientation: 'h',
      x: 0,
      y: -0.25,
      yanchor: 'top',
      bgcolor: 'rgba(255, 255, 255, 0.8)',
      bordercolor: '#BDC3C7',
      borderwidth: 1
    },
    plot_bgcolor: '#FAFAFA',
    paper_bgcolor: 'rgba(0,0,0,0)'
  };

  const config = {
    responsive: true,
    displayModeBar: true,
    displaylogo: false
  };

  container.innerHTML = '';
  Plotly.newPlot('perindex-container', traces, layout, config);
}

function renderHistogram() {
  const container = document.getElementById('hist-container');

  if (!(costModel && CostModelEvaluators[costModel.modelType])) {
    container.innerHTML =
      '<div class="error"><p>Histogram needs an evaluable cost model</p></div>';
    return;
  }

  // Net per-index time for large index counts, per-call constant subtracted
  // (the same quantity as the per-index panel above).
  const points = benchmarkData.filter(d => d.args[1] >= histThreshold);
  if (points.length === 0) {
    container.innerHTML = `<div class="error"><p>No benchmarks with index count ≥ ${histThreshold}</p></div>`;
    return;
  }

  const c0 = modelConstant();
  const perIndex = points.map(d => (d.time - overhead - c0) / d.args[1]);

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

  // Mark the model's net time per index at the histogram threshold on the
  // distribution.  The model is not linear in the index count, so this is the
  // average over the indices of one call rather than a single slope.
  if (histThreshold > 0) {
    const perIndexNs = (modelAt(histThreshold) - overhead - c0) / histThreshold;
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
    renderPerIndex();
  });

  // Y-axis mode selector
  const yAxisModeSelect = document.getElementById('y-axis-mode');
  yAxisModeSelect.addEventListener('change', (e) => {
    yAxisMode = e.target.value;
    renderPlot();
  });

  // Histogram threshold selector
  const histThresholdSelect = document.getElementById('hist-threshold');
  histThresholdSelect.addEventListener('change', (e) => {
    histThreshold = parseInt(e.target.value, 10);
    renderHistogram();
  });
}
