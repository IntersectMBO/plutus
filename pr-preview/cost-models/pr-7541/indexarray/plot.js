// IndexArray plot configuration and rendering

// Configuration
const FUNCTION_NAME = 'IndexArray';  // CSV uses PascalCase
const COST_MODEL_NAME = 'indexArray';  // JSON uses camelCase
const ARITY = 2;

// Default configuration
const DEFAULT_BRANCH = 'master';
const URL_TEMPLATE = 'https://raw.githubusercontent.com/IntersectMBO/plutus/{BRANCH}/plutus-core/cost-model/data';

// LocalStorage keys
const STORAGE_KEYS = {
  BRANCH: 'plutus-viz-branch',
  CSV_URL: 'plutus-viz-csv-url',
  JSON_URL: 'plutus-viz-json-url',
  DATA_SOURCE_COLLAPSED: 'plutus-viz-data-source-collapsed',
  PLOT_CONTROLS_COLLAPSED: 'plutus-viz-plot-controls-collapsed'
};

// Global state
let benchmarkData = [];
let modelPredictions = [];
let costModel = null;
let overhead = 0;
let showModel = true;
let yAxisMode = 'zero';

// Generate URL from template and branch
function generateUrlFromBranch(branch) {
  return URL_TEMPLATE.replace('{BRANCH}', branch);
}

// Get file URLs
function getFileUrls(baseUrl) {
  return {
    csv: `${baseUrl}/benching-conway.csv`,
    json: `${baseUrl}/builtinCostModelC.json`
  };
}

// Load settings from localStorage (URL param takes precedence)
function loadSettings() {
  const urlBranch = getBranchFromUrl();
  return {
    branch: urlBranch || localStorage.getItem(STORAGE_KEYS.BRANCH) || DEFAULT_BRANCH,
    csvUrl: localStorage.getItem(STORAGE_KEYS.CSV_URL) || '',
    jsonUrl: localStorage.getItem(STORAGE_KEYS.JSON_URL) || '',
    collapsed: localStorage.getItem(STORAGE_KEYS.DATA_SOURCE_COLLAPSED) === 'true'
  };
}

// Save settings to localStorage
function saveSettings(branch, csvUrl, jsonUrl) {
  localStorage.setItem(STORAGE_KEYS.BRANCH, branch);
  localStorage.setItem(STORAGE_KEYS.CSV_URL, csvUrl);
  localStorage.setItem(STORAGE_KEYS.JSON_URL, jsonUrl);
}

// Update URL fields based on branch name
function updateUrlsFromBranch() {
  const branchInput = document.getElementById('branch-name');
  const csvInput = document.getElementById('csv-url');
  const jsonInput = document.getElementById('json-url');

  const branch = branchInput.value.trim() || DEFAULT_BRANCH;
  const baseUrl = generateUrlFromBranch(branch);
  const urls = getFileUrls(baseUrl);

  csvInput.value = urls.csv;
  jsonInput.value = urls.json;
}

// Initialize
async function init() {
  // Load saved settings
  const settings = loadSettings();

  // Set up collapsible data source section
  const dataSourceControls = document.getElementById('data-source-controls');
  const dataSourceToggle = document.getElementById('data-source-toggle');

  if (settings.collapsed) {
    dataSourceControls.classList.add('collapsed');
  }

  dataSourceToggle.addEventListener('click', () => {
    const isCollapsed = dataSourceControls.classList.toggle('collapsed');
    localStorage.setItem(STORAGE_KEYS.DATA_SOURCE_COLLAPSED, isCollapsed);
  });

  // Set up collapsible plot controls section
  const plotControls = document.getElementById('plot-controls');
  const plotControlsToggle = document.getElementById('plot-controls-toggle');

  if (localStorage.getItem(STORAGE_KEYS.PLOT_CONTROLS_COLLAPSED) === 'true') {
    plotControls.classList.add('collapsed');
  }

  plotControlsToggle.addEventListener('click', () => {
    const isCollapsed = plotControls.classList.toggle('collapsed');
    localStorage.setItem(STORAGE_KEYS.PLOT_CONTROLS_COLLAPSED, isCollapsed);
  });

  // Set up form inputs
  const branchInput = document.getElementById('branch-name');
  const csvInput = document.getElementById('csv-url');
  const jsonInput = document.getElementById('json-url');

  // Initialize with saved or default values
  branchInput.value = settings.branch;

  if (settings.csvUrl && settings.jsonUrl) {
    csvInput.value = settings.csvUrl;
    jsonInput.value = settings.jsonUrl;
  } else {
    updateUrlsFromBranch();
  }

  // Update URLs when branch name changes
  branchInput.addEventListener('input', updateUrlsFromBranch);

  // Load data button
  const reloadButton = document.getElementById('reload-data');
  reloadButton.addEventListener('click', async () => {
    const branch = branchInput.value.trim() || DEFAULT_BRANCH;
    const csvUrl = csvInput.value.trim();
    const jsonUrl = jsonInput.value.trim();

    // Save settings
    saveSettings(branch, csvUrl, jsonUrl);

    // Load data
    await loadAndRenderData();
  });

  // Set up plot control event listeners (only once)
  setupControls();

  // Set up copy link button
  document.getElementById('copy-link').addEventListener('click', () => {
    const branch = document.getElementById('branch-name').value.trim() || DEFAULT_BRANCH;
    const url = new URL(window.location.href);
    url.search = '';
    url.searchParams.set('branch', branch);
    navigator.clipboard.writeText(url.toString());
    // Brief visual feedback
    const btn = document.getElementById('copy-link');
    const original = btn.textContent;
    btn.textContent = 'Copied!';
    setTimeout(() => btn.textContent = original, 1500);
  });

  // Initial load
  await loadAndRenderData();
}

// Load and render data
async function loadAndRenderData() {
  // Show loading state
  const container = document.getElementById('plot-container');
  container.innerHTML = '<div class="loading">Loading data and generating plot...</div>';

  try {
    // Get URLs from form inputs
    const csvUrl = document.getElementById('csv-url').value.trim();
    const jsonUrl = document.getElementById('json-url').value.trim();

    if (!csvUrl || !jsonUrl) {
      showError('Please provide both CSV and JSON file URLs');
      return;
    }

    // Load data
    const { parsedData, costModelJson, overheadMap } = await loadData(csvUrl, jsonUrl);

    // Filter for this function
    benchmarkData = filterByFunction(parsedData, FUNCTION_NAME);

    if (benchmarkData.length === 0) {
      showError(`No benchmark data found for ${FUNCTION_NAME}`);
      return;
    }

    // Extract cost model
    costModel = extractCostModel(costModelJson, COST_MODEL_NAME);

    // Get overhead
    overhead = overheadMap[ARITY] || 0;

    // Generate model predictions
    if (costModel) {
      modelPredictions = generateModelPredictions(benchmarkData, costModel, overhead);
    }

    // Update info panel
    updateInfoPanel();

    // Render plot
    renderPlot();


  } catch (error) {
    console.error('Initialization error:', error);
    showError(`Failed to load data. Check console for details. Error: ${error.message}`);
  }
}

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
  // Prepare benchmark trace - use first argument (array size) as X
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
      title: 'Array Size',
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

function showError(message) {
  const container = document.getElementById('plot-container');
  container.innerHTML = `
    <div class="error">
      <h3>Error Loading Data</h3>
      <p>${message}</p>
    </div>
  `;
}

// Start initialization when page loads
document.addEventListener('DOMContentLoaded', init);
