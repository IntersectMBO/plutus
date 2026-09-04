// Policies plot configuration and rendering

// Configuration
const FUNCTION_NAME = 'Policies';  // CSV uses PascalCase
const COST_MODEL_NAME = 'policies';  // JSON uses camelCase
const ARITY = 1;

// Global state
let benchmarkData = [];
let modelPredictions = [];
let costModel = null;
let overhead = 0;
let showModel = true;
let yAxisMode = 'zero';

setupCostModelPage({
  slug: 'policies',
  functionName: FUNCTION_NAME,
  costModelName: COST_MODEL_NAME,
  arity: ARITY,
  render(data) {
    ({ benchmarkData, costModel, overhead, modelPredictions } = data);
    updateInfoPanel();
    renderPlot();
  },
  setupControls
});

function updateInfoPanel() {
  // Calculate stats
  const stats = calculateStats(benchmarkData, 0);

  // Update data points
  document.getElementById('info-data-points').textContent = stats.dataPoints;

  // Update ranges
  if (stats.minArg !== undefined) {
    document.getElementById('info-x-range').textContent = `${stats.minArg} - ${stats.maxArg}`;
  }

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

function renderPlot() {
  // Prepare benchmark trace
  const benchmarkX = benchmarkData.map(d => d.args[0]);
  const benchmarkY = benchmarkData.map(d => d.time);

  const benchmarkTrace = {
    x: benchmarkX,
    y: benchmarkY,
    mode: 'markers',
    type: 'scatter',
    name: 'Benchmark Data',
    marker: {
      size: 6,
      color: '#0033AD',
      opacity: 0.7
    }
  };

  const traces = [benchmarkTrace];

  // Prepare model trace if available
  if (showModel && modelPredictions.length > 0) {
    const modelX = modelPredictions.map(d => d.args[0]);
    const modelY = modelPredictions.map(d => d.predictedTime);

    const modelTrace = {
      x: modelX,
      y: modelY,
      mode: 'markers',
      type: 'scatter',
      name: 'Model Predictions',
      marker: {
        size: 6,
        color: '#E53E3E',
        opacity: 0.4,
        symbol: 'x'
      }
    };

    traces.push(modelTrace);
  }

  // Layout configuration
  const layout = {
    title: {
      text: `${FUNCTION_NAME} - Benchmark vs Model`,
      font: { size: 20 }
    },
    xaxis: {
      title: 'Value Size',
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
    layout.yaxis.range = [0, Math.max(...benchmarkY) * 1.1];
  } else {
    const minY = Math.min(...benchmarkY);
    const maxY = Math.max(...benchmarkY);
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
  // Clear loading message
  const container = document.getElementById('plot-container');
  container.innerHTML = '';
  Plotly.newPlot('plot-container', traces, layout, config);
}

function setupControls() {
  // Show/hide model checkbox
  const showModelCheckbox = document.getElementById('show-model');
  showModelCheckbox.addEventListener('change', (e) => {
    showModel = e.target.checked;
    renderPlot();
  });

  // Y-axis mode selector
  const yAxisModeSelect = document.getElementById('y-axis-mode');
  yAxisModeSelect.addEventListener('change', (e) => {
    yAxisMode = e.target.value;
    renderPlot();
  });
}
