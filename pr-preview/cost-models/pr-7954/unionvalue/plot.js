// UnionValue plot configuration and rendering (3D)

// Configuration
const FUNCTION_NAME = 'UnionValue';  // CSV uses PascalCase
const COST_MODEL_NAME = 'unionValue';  // JSON uses camelCase
const ARITY = 2;

// Global state
let benchmarkData = [];
let shippedModel = null;
let costModel = null; // the shipped model, or the coefficients typed into the info panel
let overhead = 0;
let zAxisMode = 'zero';

setupCostModelPage({
  slug: 'unionvalue',
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
  // Calculate stats
  const stats = calculateStats(benchmarkData);

  // Update data points
  document.getElementById('info-data-points').textContent = stats.dataPoints;

  // Update ranges for X and Y axes (Value sizes)
  if (benchmarkData.length > 0) {
    const xValues = benchmarkData.map(d => d.args[0]);
    const yValues = benchmarkData.map(d => d.args[1]);

    const minX = Math.min(...xValues);
    const maxX = Math.max(...xValues);
    const minY = Math.min(...yValues);
    const maxY = Math.max(...yValues);

    document.getElementById('info-x-range').textContent = `${minX} - ${maxX}`;
    document.getElementById('info-y-range').textContent = `${minY} - ${maxY}`;
  }

  document.getElementById('info-time-range').textContent = stats.timeRange;

  renderFitSummary(costModel, shippedModel, benchmarkData, overhead);

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
      `${overhead.toFixed(2)} ns (arity ${ARITY})`;
  } else {
    document.getElementById('info-overhead').textContent = 'Not calculated';
  }
}

function renderPlot() {
  // Prepare benchmark trace (3D scatter)
  const benchmarkX = benchmarkData.map(d => d.args[0]);
  const benchmarkY = benchmarkData.map(d => d.args[1]);
  const benchmarkZ = benchmarkData.map(d => d.time);

  const benchmarkTrace = {
    x: benchmarkX,
    y: benchmarkY,
    z: benchmarkZ,
    mode: 'markers',
    type: 'scatter3d',
    name: 'Benchmark Data',
    marker: {
      size: 4,
      color: '#0033AD',
      opacity: 0.7
    }
  };

  const traces = [benchmarkTrace];

  const modelTrace = modelTrace3d(costModel, benchmarkData, overhead);
  if (modelTrace) traces.push(modelTrace);

  // Layout configuration
  const layout = {
    // A constant `uirevision` keeps the camera the reader has rotated to across re-renders.
    uirevision: FUNCTION_NAME,
    title: {
      text: `${FUNCTION_NAME} - Benchmark vs Model (3D)`,
      font: { size: 20 }
    },
    scene: {
      xaxis: {
        title: 'Value 1 total size',
        gridcolor: '#E0E0E0'
      },
      yaxis: {
        title: 'Value 2 total size',
        gridcolor: '#E0E0E0'
      },
      zaxis: {
        title: 'Time (nanoseconds)',
        gridcolor: '#E0E0E0'
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

  // Set Z-axis range based on mode, the model included.
  const allZ = traces.flatMap(t => t.z.flat()).filter(z => z !== null);
  if (zAxisMode === 'zero') {
    layout.scene.zaxis.range = [0, Math.max(...allZ) * 1.1];
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

  // The first render replaces the loading message; later ones update the plot in place.
  const container = document.getElementById('plot-container');
  if (!container.data) container.innerHTML = '';
  Plotly.react('plot-container', traces, layout, config);
}

function setupControls() {
  setupModelDisplay(renderPlot);

  // Z-axis mode selector
  const zAxisModeSelect = document.getElementById('z-axis-mode');
  zAxisModeSelect.addEventListener('change', (e) => {
    zAxisMode = e.target.value;
    renderPlot();
  });
}
