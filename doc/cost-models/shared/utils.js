// Shared utilities for Plutus Cost Model Visualization

/**
 * Parse CSV data from benching-conway.csv
 * Format: benchmark,t,t.mean.lb,t.mean.ub,t.sd,t.sd.lb,t.sd.ub
 * Where benchmark is FunctionName/Arg1/Arg2/.../ArgN
 * Returns array of objects: { function, args: [arg1, arg2, ...], time }
 */
function parseCSV(csvText) {
  const lines = csvText.trim().split('\n');
  const results = [];

  for (const line of lines) {
    const trimmedLine = line.trim();
    // Skip comments and header
    if (!trimmedLine || trimmedLine.startsWith('#') || trimmedLine.startsWith('benchmark')) {
      continue;
    }

    const parts = trimmedLine.split(',');
    if (parts.length < 2) continue;

    const pathParts = parts[0].trim().split('/');
    const functionName = pathParts[0];
    const args = pathParts.slice(1).map(arg => parseFloat(arg));

    // Second column is 't' (mean execution time in seconds)
    const timeSeconds = parseFloat(parts[1].trim());

    if (!isNaN(timeSeconds)) {
      // Convert from seconds to nanoseconds
      const timeNanoseconds = timeSeconds * 1e9;
      results.push({ function: functionName, args, time: timeNanoseconds });
    }
  }

  return results;
}

/**
 * Filter parsed CSV data for a specific function
 */
function filterByFunction(parsedData, functionName) {
  return parsedData.filter(row => row.function === functionName);
}

/**
 * Calculate overhead from Nop benchmarks
 * Returns a map of arity -> overhead (in nanoseconds)
 * Nop benchmarks are named Nop1b, Nop2b, Nop3b, etc. where the number indicates arity
 */
function calculateOverhead(parsedData) {
  const overheadMap = {};

  // Match Nop functions: Nop1o, Nop2o, Nop3o, etc. (Opaque args, matching R's models.R)
  const nopPattern = /^Nop(\d+)o$/;

  for (const row of parsedData) {
    const match = row.function.match(nopPattern);
    if (match) {
      const arity = parseInt(match[1], 10);
      if (!overheadMap[arity]) {
        overheadMap[arity] = [];
      }
      overheadMap[arity].push(row.time);
    }
  }

  // Calculate average for each arity
  const result = {};
  for (const [arity, times] of Object.entries(overheadMap)) {
    const avg = times.reduce((sum, t) => sum + t, 0) / times.length;
    result[arity] = avg;
  }

  return result;
}

/**
 * Cost model evaluators
 * Each function takes coefficients object and args array
 * Supports both c0/c1/c2 and intercept/slope naming conventions
 */
const CostModelEvaluators = {
  constant_cost: (coeffs, args) => {
    return coeffs.c0 || coeffs.intercept || 0;
  },

  linear_in_x: (coeffs, args) => {
    const c0 = coeffs.c0 || coeffs.intercept || 0;
    const c1 = coeffs.c1 || coeffs.slope || 0;
    return c0 + c1 * args[0];
  },

  linear_in_y: (coeffs, args) => {
    const c0 = coeffs.c0 || coeffs.intercept || 0;
    const c1 = coeffs.c1 || coeffs.slope || 0;
    return c0 + c1 * args[1];
  },

  linear_in_z: (coeffs, args) => {
    const c0 = coeffs.c0 || coeffs.intercept || 0;
    const c1 = coeffs.c1 || coeffs.slope || 0;
    return c0 + c1 * args[2];
  },

  quadratic_in_x: (coeffs, args) => {
    const x = args[0];
    return (coeffs.c0 || 0) + (coeffs.c1 || 0) * x + (coeffs.c2 || 0) * x * x;
  },

  quadratic_in_y: (coeffs, args) => {
    const y = args[1];
    return (coeffs.c0 || 0) + (coeffs.c1 || 0) * y + (coeffs.c2 || 0) * y * y;
  },

  quadratic_in_z: (coeffs, args) => {
    const z = args[2];
    return (coeffs.c0 || 0) + (coeffs.c1 || 0) * z + (coeffs.c2 || 0) * z * z;
  },

  linear_in_xy: (coeffs, args) => {
    return (coeffs.c0 || 0) + (coeffs.c1 || 0) * args[0] + (coeffs.c2 || 0) * args[1];
  },

  linear_in_xz: (coeffs, args) => {
    return (coeffs.c0 || 0) + (coeffs.c1 || 0) * args[0] + (coeffs.c2 || 0) * args[2];
  },

  linear_in_yz: (coeffs, args) => {
    return (coeffs.c0 || 0) + (coeffs.c1 || 0) * args[1] + (coeffs.c2 || 0) * args[2];
  },

  added_sizes: (coeffs, args) => {
    // added_sizes models cost as linear in sum of sizes
    const sum = args.reduce((a, b) => a + b, 0);
    const c0 = coeffs.c0 || coeffs.intercept || 0;
    const c1 = coeffs.c1 || coeffs.slope || 0;
    return c0 + c1 * sum;
  },

  multiplied_sizes: (coeffs, args) => {
    // multiplied_sizes models cost as linear in product of sizes
    const product = args.reduce((a, b) => a * b, 1);
    const c0 = coeffs.c0 || coeffs.intercept || 0;
    const c1 = coeffs.c1 || coeffs.slope || 0;
    return c0 + c1 * product;
  },

  min_size: (coeffs, args) => {
    const min = Math.min(...args);
    const c0 = coeffs.c0 || coeffs.intercept || 0;
    const c1 = coeffs.c1 || coeffs.slope || 0;
    return c0 + c1 * min;
  },

  max_size: (coeffs, args) => {
    const max = Math.max(...args);
    const c0 = coeffs.c0 || coeffs.intercept || 0;
    const c1 = coeffs.c1 || coeffs.slope || 0;
    return c0 + c1 * max;
  },

  linear_in_max_yz: (coeffs, args) => {
    const max_yz = Math.max(args[1], args[2]);
    return (coeffs.c0 || 0) + (coeffs.c1 || 0) * args[0] + (coeffs.c2 || 0) * max_yz;
  },

  linear_in_x_and_y: (coeffs, args) => {
    const intercept = coeffs.intercept || coeffs.c0 || 0;
    const slope1 = coeffs.slope1 || coeffs.c1 || 0;
    const slope2 = coeffs.slope2 || coeffs.c2 || 0;
    return intercept + slope1 * args[0] + slope2 * args[1];
  },

  const_above_diagonal: (coeffs, args) => {
    // Above diagonal: x < y, return constant
    // Below/on diagonal: x >= y, use inner model
    if (args[0] < args[1]) {
      return coeffs.constant || 0;
    }
    // Use inner model
    const innerModel = coeffs.model;
    if (innerModel && CostModelEvaluators[innerModel.type]) {
      return CostModelEvaluators[innerModel.type](innerModel.arguments, args);
    }
    return 0;
  },

  const_below_diagonal: (coeffs, args) => {
    // Below diagonal: x > y, return constant
    // Above/on diagonal: x <= y, use inner model
    if (args[0] > args[1]) {
      return coeffs.constant || 0;
    }
    // Use inner model
    const innerModel = coeffs.model;
    if (innerModel && CostModelEvaluators[innerModel.type]) {
      return CostModelEvaluators[innerModel.type](innerModel.arguments, args);
    }
    return 0;
  },

  // c00 + c10*x + c01*y + c11*x*y, the coefficient names the JSON uses
  // (TwoVariableWithInteractionFunction in CostingFun.Core).
  with_interaction_in_x_and_y: (coeffs, args) => {
    return (coeffs.c00 ?? 0)
      + (coeffs.c10 ?? 0) * args[0]
      + (coeffs.c01 ?? 0) * args[1]
      + (coeffs.c11 ?? 0) * args[0] * args[1];
  },

  linear_in_u: (coeffs, args) => {
    // linear_in_u is linear in the fourth argument (args[3])
    // The "u" refers to the fourth parameter's cost stream
    const c0 = coeffs.c0 ?? coeffs.intercept ?? 0;
    const c1 = coeffs.c1 ?? coeffs.slope ?? 0;
    const u = args.length > 3 ? args[3] : 0;
    return c0 + c1 * u;
  }
};

/**
 * Evaluate cost model for given arguments
 * Returns cost in picoseconds
 */
function evaluateCostModel(modelType, coefficients, args) {
  const evaluator = CostModelEvaluators[modelType];
  if (!evaluator) {
    console.error(`Unsupported cost model type: ${modelType}`);
    return null;
  }

  try {
    return evaluator(coefficients, args);
  } catch (error) {
    console.error(`Error evaluating cost model: ${error}`);
    return null;
  }
}

/**
 * Extract cost model from builtinCostModelE.json for a specific function
 * Returns { modelType, coefficients } or null if not found
 */
function extractCostModel(costModelJson, functionName) {
  // The JSON structure is: { functionName: { cpu: { type: "...", arguments: ... } } }
  if (!costModelJson[functionName]) {
    console.error(`Function ${functionName} not found in cost model`);
    return null;
  }

  const cpuModel = costModelJson[functionName].cpu;
  if (!cpuModel) {
    console.error(`CPU model not found for ${functionName}`);
    return null;
  }

  // Handle different argument formats
  let coefficients = {};
  if (typeof cpuModel.arguments === 'number') {
    // For constant_cost, arguments is just a number
    coefficients.c0 = cpuModel.arguments;
  } else if (typeof cpuModel.arguments === 'object') {
    // For other models, arguments is an object with coefficients
    coefficients = cpuModel.arguments;
  }

  return {
    modelType: cpuModel.type,
    coefficients: coefficients
  };
}

/**
 * Generate model predictions for the same input points as benchmark data
 * Returns array of { args, predictedTime } where predictedTime is in nanoseconds
 *
 * Note: The cost model represents NET cost (after overhead subtraction during fitting).
 * To compare with benchmark data, we need to add the overhead back.
 */
function generateModelPredictions(benchmarkData, costModel, overhead) {
  if (!costModel) return [];

  const predictions = [];

  for (const dataPoint of benchmarkData) {
    const costPicoseconds = evaluateCostModel(
      costModel.modelType,
      costModel.coefficients,
      dataPoint.args
    );

    if (costPicoseconds !== null) {
      // Convert picoseconds to nanoseconds
      const costNanoseconds = costPicoseconds / 1000;

      // Add overhead to get total predicted time (to match benchmark measurements)
      const totalTime = costNanoseconds + (overhead || 0);

      predictions.push({
        args: dataPoint.args,
        predictedTime: totalTime
      });
    }
  }

  return predictions;
}

// The model of a two-argument builtin as a translucent surface over the plane the
// benchmark points span.
function modelSurfaceTrace(model, points, overhead, options = {}) {
  const { xLog = false, xSteps = 40, ySteps = 20, name = 'Model surface' } = options;
  const xs = points.map(p => p.args[0]);
  const ys = points.map(p => p.args[1]);
  const spread = (lo, hi, n, log) => {
    if (log) {
      lo = Math.max(lo, 1);
      const a = Math.log(lo), b = Math.log(hi);
      return Array.from({ length: n }, (_, i) => Math.exp(a + (b - a) * i / (n - 1)));
    }
    return Array.from({ length: n }, (_, i) => lo + (hi - lo) * i / (n - 1));
  };
  const xGrid = spread(Math.min(...xs), Math.max(...xs), xSteps, xLog);
  const distinctY = [...new Set(ys)].sort((a, b) => a - b);
  const yGrid = distinctY.length <= ySteps
    ? distinctY
    : spread(Math.min(...ys), Math.max(...ys), ySteps, false);
  return {
    type: 'surface',
    name,
    x: xGrid,
    y: yGrid,
    z: yGrid.map(y => xGrid.map(x => modelCharge(model, [x, y], overhead))),
    opacity: 0.35,
    colorscale: [[0, '#E53E3E'], [1, '#E53E3E']],
    showscale: false,
    showlegend: true,
    hovertemplate: '%{x:.3s}, %{y}<br>charged %{z:.3s} ns<extra></extra>'
  };
}

// Markup for one row of radio buttons: a label, then one `<label><input></label>` per
// option.
function radioGroup(title, name, options, selected) {
  return `<span class="radio-title">${title}</span>` + options.map(([value, text]) =>
    `<label class="radio"><input type="radio" name="${name}" value="${value}"` +
    `${value === selected ? ' checked' : ''}> ${text}</label>`).join('');
}

// How the pages draw a two-argument model: not at all, as a red cross at every benchmark
// point, or as the surface of `modelSurfaceTrace`.
let modelDisplay = 'surface';

// Replace the page's "show model" checkbox with the Hidden / Points / Surface radio group
// and re-render on change.
function setupModelDisplay(rerender) {
  const showModel = document.getElementById('show-model');
  if (!showModel) return;
  const group = showModel.closest('.control-group');
  group.classList.add('radio-group');
  group.innerHTML = radioGroup('Cost model:', 'model-display',
    [['hidden', 'Hidden'], ['points', 'Points'], ['surface', 'Surface']], modelDisplay);
  group.querySelectorAll('input[name="model-display"]').forEach(r =>
    r.addEventListener('change', e => { modelDisplay = e.target.value; rerender(); }));
}

// The model's trace for a two-argument page, or null when the model is hidden or missing.
function modelTrace3d(model, points, overhead, options = {}) {
  const { xLog = false, hover } = options;
  if (!model || modelDisplay === 'hidden') return null;
  if (modelDisplay === 'surface') return modelSurfaceTrace(model, points, overhead, { xLog });
  const trace = {
    x: points.map(d => d.args[0]),
    y: points.map(d => d.args[1]),
    z: points.map(d => modelCharge(model, d.args, overhead)),
    mode: 'markers',
    type: 'scatter3d',
    name: 'Model Predictions',
    marker: { size: 4, color: '#E53E3E', opacity: 0.6, symbol: 'x' }
  };
  if (hover) trace.hovertemplate = hover;
  return trace;
}

// A model's predicted total time in nanoseconds for one benchmark point, overhead
// included, or null when it cannot be evaluated.
function modelCharge(model, args, overhead) {
  if (!model) return null;
  const ps = evaluateCostModel(model.modelType, model.coefficients, args);
  return ps === null ? null : ps / 1000 + overhead;
}

function median(values) {
  if (values.length === 0) return 0;
  const sorted = [...values].sort((a, b) => a - b);
  return sorted[Math.floor(sorted.length / 2)];
}

/**
 * One info-panel block per fit: the charge line, then how many points the model over- and
 * undercharges, with the median and worst factor on each side. An overcharge is charged /
 * measured, an undercharge measured / charged.
 */
function fitSummary(name, model, points, overhead, terms) {
  if (!model) return `<p>${name}: not available</p>`;
  const c = model.coefficients;
  const over = [];   // charged / measured, for the points charged at least what they cost
  const under = [];  // measured / charged, for the points charged less than they cost
  for (const d of points) {
    const predicted = modelCharge(model, d.args, overhead);
    if (predicted === null) return `<p>${name}: not evaluable (${model.modelType})</p>`;
    if (predicted >= d.time) over.push(predicted / d.time);
    else under.push(d.time / predicted);
  }
  const fmt = v => v.toLocaleString('en-US', { maximumFractionDigits: 0 });
  const oneSlope = terms && Object.keys(c).sort().join() === 'intercept,slope';
  const charge = oneSlope
    ? `${fmt(c.intercept)} + ${fmt(c.slope)}&middot;${terms.join('&middot;')}`
    : formatModelFormula(model.modelType, c);
  const total = points.length;
  const count = xs => `${xs.length} &middot; ${total ? Math.round(100 * xs.length / total) : 0}%`;
  const factor = (xs, pick) => xs.length ? `${pick(xs).toFixed(2)}x` : '&mdash;';
  return `
    <p><strong>${name}</strong></p>
    <dl>
      <dt>Charge (ps):</dt>
      <dd>${charge}</dd>
    </dl>
    <table class="fit-table">
      <thead>
        <tr>
          <th></th>
          <th title="Points charged at least what they measured; the factor is charged / measured.">Overcharged</th>
          <th title="Points charged less than they measured; the factor is measured / charged.">Undercharged</th>
        </tr>
      </thead>
      <tbody>
        <tr><th>Points</th><td>${count(over)}</td><td>${count(under)}</td></tr>
        <tr><th>Median</th><td>${factor(over, median)}</td><td>${factor(under, median)}</td></tr>
        <tr><th>Worst</th><td>${factor(over, xs => Math.max(...xs))}</td><td>${factor(under, xs => Math.max(...xs))}</td></tr>
      </tbody>
    </table>`;
}

// The fit summary of `model` against `points`, written into `#fit-comparison`.
function renderFitSummary(model, shipped, points, overhead, terms) {
  let el = document.getElementById('fit-comparison');
  if (!el) {
    const type = document.getElementById('info-model-type');
    if (!type) return;
    const section = document.createElement('div');
    section.className = 'info-section';
    section.innerHTML = '<h3>Model against the benchmark</h3><div id="fit-comparison"></div>';
    type.closest('.info-section').insertAdjacentElement('beforebegin', section);
    el = document.getElementById('fit-comparison');
  }
  const same = shipped && model &&
    JSON.stringify(model.coefficients) === JSON.stringify(shipped.coefficients);
  const name = same ? 'Shipped model' : 'Edited coefficients';
  el.innerHTML = fitSummary(name, model, points, overhead, terms);
}

/**
 * One number input per coefficient of the shipped model, plus a button that puts the
 * shipped values back. Editing a value calls `onChange` with a copy of the model carrying
 * the edited coefficients; nothing is written anywhere.
 */
function renderCoefficientEditor(shipped, onChange) {
  const formula = document.getElementById('info-model-formula');
  if (!formula || !shipped) return;
  let dd = document.getElementById('info-model-coefficients');
  if (!dd) {
    formula.insertAdjacentHTML('afterend',
      '<dt>Coefficients (editable):</dt><dd id="info-model-coefficients"></dd>');
    dd = document.getElementById('info-model-coefficients');
  }
  const keys = Object.keys(shipped.coefficients);
  const stepTitle = 'by 1% of the current value; Shift: 10%, Alt: 0.1%';
  dd.innerHTML = keys.map(k =>
    `<div class="coefficient-row"><span class="coefficient-name">${k}</span>` +
    `<span class="coefficient-controls">` +
    `<button type="button" class="step" data-for="${k}" data-direction="-1" title="Lower ${stepTitle}">&minus;%</button>` +
    `<input type="number" step="1" data-coefficient="${k}" value="${shipped.coefficients[k]}" aria-label="${k}">` +
    `<button type="button" class="step" data-for="${k}" data-direction="1" title="Raise ${stepTitle}">+%</button>` +
    `</span></div>`).join('') +
    '<div class="coefficient-row"><span></span>' +
    '<button type="button" class="secondary" id="reset-coefficients">Reset to shipped</button></div>';
  const current = () => {
    const c = {};
    dd.querySelectorAll('input[data-coefficient]').forEach(i => {
      const v = Number(i.value);
      c[i.dataset.coefficient] = Number.isFinite(v) ? v : shipped.coefficients[i.dataset.coefficient];
    });
    return { ...shipped, coefficients: c };
  };
  // The buttons and the arrow keys move by a share of the current value, rounded to a
  // whole picosecond and never below one.
  const bump = (input, direction, event) => {
    const share = event.shiftKey ? 0.1 : event.altKey ? 0.001 : 0.01;
    const v = Number(input.value);
    const base = Number.isFinite(v) ? v : shipped.coefficients[input.dataset.coefficient];
    const delta = Math.max(1, Math.round(Math.abs(base) * share));
    input.value = Math.max(0, base + direction * delta);
    onChange(current());
  };
  dd.querySelectorAll('input').forEach(i => {
    i.addEventListener('input', () => onChange(current()));
    i.addEventListener('keydown', e => {
      if (e.key !== 'ArrowUp' && e.key !== 'ArrowDown') return;
      e.preventDefault();
      bump(i, e.key === 'ArrowUp' ? 1 : -1, e);
    });
  });
  dd.querySelectorAll('button.step').forEach(b => b.addEventListener('click', e => {
    bump(dd.querySelector(`input[data-coefficient="${b.dataset.for}"]`), Number(b.dataset.direction), e);
  }));
  dd.querySelector('#reset-coefficients').addEventListener('click', () => {
    keys.forEach(k => { dd.querySelector(`input[data-coefficient="${k}"]`).value = shipped.coefficients[k]; });
    onChange(current());
  });
}

// The shared loader overwrites `#plot-container`, so the plot div is the page's to create.
function ensurePlotPanel(id) {
  if (document.getElementById(id)) return;
  const container = document.getElementById('plot-container');
  container.innerHTML = '';
  const panel = document.createElement('div');
  panel.id = id;
  container.appendChild(panel);
}

/**
 * Wire up a page for a builtin charged on the product of its policy list's length and the
 * depth of its `Value`'s outer map (`keepPolicies`, `dropPolicies`): the benchmark as a 3D
 * scatter, the model as points or a surface, the fit table and the coefficient editor.
 *
 * @param {Object} page
 * @param {string} page.slug           Directory name, used to highlight the nav
 * @param {string} page.functionName   Benchmark name (PascalCase, as in the CSV)
 * @param {string} page.costModelName  Cost model key (camelCase, as in the JSON)
 */
function setupPolicyFilterPage({ slug, functionName, costModelName }) {
  const arity = 2;
  const plotConfig = { responsive: true, displayModeBar: true, displaylogo: false };

  let benchmarkData = [];
  let shippedModel = null;
  let costModel = null; // the shipped model, or the coefficients typed into the info panel
  let overhead = 0;
  let axisScale = 'linear';

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
      ? `${overhead.toFixed(2)} ns (arity ${arity})`
      : 'Not calculated';

    // Every point is in the fit.
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

  /* Sizes on the horizontal axes, time on the vertical one; measured and charged at each
  point. */
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

  function renderPlot() {
    ensurePlotPanel('plot-3d');
    const scaled = axisScale;
    const suffix = axisScale === 'log' ? ', log' : '';
    Plotly.react('plot-3d', plotTraces(), {
      // A constant `uirevision` keeps the camera the reader has rotated to across re-renders.
      uirevision: functionName,
      title: { text: `${functionName} - Benchmark vs Model (3D)`, font: { size: 20 } },
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
    }, plotConfig);
  }

  function setupControls() {
    setupModelDisplay(renderPlot);
    document.querySelectorAll('input[name="axis-scale"]').forEach(r =>
      r.addEventListener('change', e => {
        axisScale = e.target.value;
        renderPlot();
      }));
  }

  setupCostModelPage({
    slug,
    functionName,
    costModelName,
    arity,
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
}

/**
 * Format model formula as human-readable string
 */
function formatModelFormula(modelType, coefficients) {
  const formatCoeff = (val) => {
    if (val >= 1000) {
      return val.toLocaleString('en-US', { maximumFractionDigits: 0 });
    }
    return val.toLocaleString('en-US', { maximumFractionDigits: 2 });
  };

  // Support both c0/c1/c2 and intercept/slope naming
  const c0 = coefficients.c0 || coefficients.intercept || 0;
  const c1 = coefficients.c1 || coefficients.slope || 0;
  const c2 = coefficients.c2 || 0;

  switch (modelType) {
    case 'constant_cost':
      return `${formatCoeff(c0)} picoseconds`;

    case 'linear_in_x':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (arg1) picoseconds`;

    case 'linear_in_y':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (arg2) picoseconds`;

    case 'linear_in_z':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (arg3) picoseconds`;

    case 'quadratic_in_x':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (arg1) + ${formatCoeff(c2)} × (arg1)² picoseconds`;

    case 'quadratic_in_y':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (arg2) + ${formatCoeff(c2)} × (arg2)² picoseconds`;

    case 'quadratic_in_z':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (arg3) + ${formatCoeff(c2)} × (arg3)² picoseconds`;

    case 'linear_in_xy':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (arg1) + ${formatCoeff(c2)} × (arg2) picoseconds`;

    case 'linear_in_xz':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (arg1) + ${formatCoeff(c2)} × (arg3) picoseconds`;

    case 'linear_in_yz':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (arg2) + ${formatCoeff(c2)} × (arg3) picoseconds`;

    case 'added_sizes':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (sum of args) picoseconds`;

    case 'multiplied_sizes':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (product of args) picoseconds`;

    case 'min_size':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (min of args) picoseconds`;

    case 'max_size':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (max of args) picoseconds`;

    case 'linear_in_max_yz':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (arg1) + ${formatCoeff(c2)} × max(arg2, arg3) picoseconds`;

    case 'linear_in_x_and_y': {
      const intercept = coefficients.intercept || coefficients.c0 || 0;
      const slope1 = coefficients.slope1 || coefficients.c1 || 0;
      const slope2 = coefficients.slope2 || coefficients.c2 || 0;
      return `${formatCoeff(intercept)} + ${formatCoeff(slope1)} × (arg1) + ${formatCoeff(slope2)} × (arg2) picoseconds`;
    }

    case 'const_above_diagonal': {
      const constant = coefficients.constant || 0;
      const innerModel = coefficients.model;
      const innerFormula = innerModel ? formatModelFormula(innerModel.type, innerModel.arguments) : 'unknown';
      return `if arg1 < arg2: ${formatCoeff(constant)} picoseconds, else: ${innerFormula}`;
    }

    case 'const_below_diagonal': {
      const constant = coefficients.constant || 0;
      const innerModel = coefficients.model;
      const innerFormula = innerModel ? formatModelFormula(innerModel.type, innerModel.arguments) : 'unknown';
      return `if arg1 > arg2: ${formatCoeff(constant)} picoseconds, else: ${innerFormula}`;
    }

    case 'with_interaction_in_x_and_y': {
      const c00 = coefficients.c00 ?? 0;
      const c10 = coefficients.c10 ?? 0;
      const c01 = coefficients.c01 ?? 0;
      const c11 = coefficients.c11 ?? 0;
      return `${formatCoeff(c00)} + ${formatCoeff(c10)} × (arg1) + ${formatCoeff(c01)} × (arg2) + ${formatCoeff(c11)} × (arg1×arg2) picoseconds`;
    }

    case 'linear_in_u':
      return `${formatCoeff(c0)} + ${formatCoeff(c1)} × (arg4) picoseconds`;

    default:
      return `${modelType} (formula not yet implemented)`;
  }
}

/**
 * Calculate statistics from benchmark data
 */
function calculateStats(data, argIndex = null) {
  if (data.length === 0) return {};

  const times = data.map(d => d.time);
  const minTime = Math.min(...times);
  const maxTime = Math.max(...times);

  const stats = {
    dataPoints: data.length,
    minTime: minTime,
    maxTime: maxTime,
    timeRange: `${(minTime / 1000).toFixed(2)} µs - ${(maxTime / 1000).toFixed(2)} µs`
  };

  if (argIndex !== null && data[0].args.length > argIndex) {
    const argValues = data.map(d => d.args[argIndex]);
    stats.minArg = Math.min(...argValues);
    stats.maxArg = Math.max(...argValues);
  }

  return stats;
}

/**
 * Load data from URLs
 */
async function loadData(csvUrl, jsonUrl) {
  try {
    const [csvResponse, jsonResponse] = await Promise.all([
      fetch(csvUrl),
      fetch(jsonUrl)
    ]);

    // Include status and URL: a stale saved branch (deleted after its PR
    // merges) is the routine failure here, and the URL is what reveals it.
    if (!csvResponse.ok) {
      throw new Error(`CSV request returned HTTP ${csvResponse.status} for ${csvUrl}`);
    }

    if (!jsonResponse.ok) {
      throw new Error(`JSON request returned HTTP ${jsonResponse.status} for ${jsonUrl}`);
    }

    const csvText = await csvResponse.text();
    const costModelJson = await jsonResponse.json();

    const parsedData = parseCSV(csvText);

    return {
      parsedData,
      costModelJson,
      overheadMap: calculateOverhead(parsedData)
    };
  } catch (error) {
    console.error('Error loading data:', error);
    throw error;
  }
}

/**
 * Get branch name from URL query parameter
 * @returns {string|null} Branch name or null if not specified
 */
function getBranchFromUrl() {
  const params = new URLSearchParams(window.location.search);
  return params.get('branch');
}

// ============================================================================
// Shared page plumbing
// ============================================================================
// Every builtin page has the same navigation, data-source controls, URL
// scheme and loading flow; a page supplies only its identity and rendering.
// Adding a builtin page or switching to a new cost model file is done here,
// in one place.

const DEFAULT_BRANCH = 'master';
const URL_TEMPLATE = 'https://raw.githubusercontent.com/IntersectMBO/plutus/{BRANCH}/plutus-core/cost-model/data';
const GITHUB_DATA_URL = 'https://github.com/IntersectMBO/plutus/blob/master/plutus-core/cost-model/data';

const BENCH_CSV_FILE = 'benching-conway.csv';
// Variant E is the PlutusV3 cost model from the vanRossem hard fork (PV 11)
// onwards (C is the previous V3 era).
const COST_MODEL_FILE = 'builtinCostModelE.json';
const COST_MODEL_NOTE = '(PlutusV3 from PV 11 / vanRossem)';

// One entry per builtin page, in navigation order: [slug, label, description].  Both the
// nav bar and the landing page's function list are generated from this, so adding a page
// means adding one entry here and nothing else.
const PAGES = [
  ['valuedata', 'ValueData',
   'Converts a Plutus <code>Value</code> to <code>Data</code> representation. ' +
   '(2D visualization: Value Size vs Time)'],
  ['unvaluedata', 'UnValueData',
   'Converts <code>Data</code> representation back to a Plutus <code>Value</code>. ' +
   '(2D visualization: Data Size vs Time)'],
  ['valuecontains', 'ValueContains',
   'Checks if a Plutus <code>Value</code> (haystack) contains another <code>Value</code> ' +
   '(needle). (3D visualization: Container Size \u00d7 Contained Size \u00d7 Time)'],
  ['lookupcoin', 'LookupCoin',
   'Looks up a specific coin (currency symbol and token name) in a Plutus ' +
   '<code>Value</code>. (2D visualization: Value Size vs Time)'],
  ['insertcoin', 'InsertCoin',
   'Inserts a coin into a Plutus <code>Value</code> map structure. ' +
   '(2D visualization: Value Size vs Time)'],
  ['unionvalue', 'UnionValue',
   'Unions two Plutus <code>Value</code> structures into one. ' +
   '(3D visualization: Value Size \u00d7 Value Size \u00d7 Time)'],
  ['scalevalue', 'ScaleValue',
   'Multiplies a Plutus <code>Value</code> by a scalar, scaling all quantities. ' +
   '(2D visualization: Value Size vs Time)'],
  ['assetcount', 'AssetCount',
   'Returns the number of <code>(currency symbol, token name)</code> pairs in a Plutus ' +
   '<code>Value</code> in O(1) time. ' +
   '(2D visualization: Value Size vs Time - constant cost)'],
  ['policies', 'Policies',
   'Returns the currency symbols of a Plutus <code>Value</code>; linear in the number ' +
   'of policies. (2D visualization: Policy Count vs Time)'],
  ['keeppolicies', 'KeepPolicies',
   'Retains only the listed currencies of a Plutus <code>Value</code>; one outer-map ' +
   'descent per element of the list. ' +
   '(3D visualization: List Length \u00d7 Outer Map Depth \u00d7 Time)'],
  ['droppolicies', 'DropPolicies',
   'Removes the listed currencies from a Plutus <code>Value</code>; one outer-map ' +
   'descent per element of the list. ' +
   '(3D visualization: List Length \u00d7 Outer Map Depth \u00d7 Time)'],
  ['listtoarray', 'ListToArray',
   'Converts a Plutus list to an array representation. ' +
   '(2D visualization: List Size vs Time)'],
  ['lengthofarray', 'LengthOfArray',
   'Returns the length of a Plutus array in O(1) time. ' +
   '(2D visualization: Array Size vs Time - constant cost)'],
  ['indexarray', 'IndexArray',
   'Retrieves an element at a given index from a Plutus array in O(1) time. ' +
   '(2D visualization: Array Size vs Time - constant cost)'],
  ['multiindexarray', 'MultiIndexArray',
   'Looks up a list of indices in a Plutus array; linear in the number of indices, ' +
   'independent of the array size. (3D visualization: Haystack Size \u00d7 Needles Size ' +
   'vs Time, plus per-index time distribution histogram)'],
  ['indexbytestring', 'IndexByteString',
   'Retrieves a byte at a given index from a ByteString in O(1) time. Performs a bounds ' +
   'check and returns the byte value (Word8). ' +
   '(2D visualization: ByteString Size vs Time - constant cost)']
];

// LocalStorage keys
const STORAGE_KEYS = {
  BRANCH: 'plutus-viz-branch',
  CSV_URL: 'plutus-viz-csv-url',
  JSON_URL: 'plutus-viz-json-url',
  DATA_SOURCE_COLLAPSED: 'plutus-viz-data-source-collapsed',
  PLOT_CONTROLS_COLLAPSED: 'plutus-viz-plot-controls-collapsed'
};

function generateUrlFromBranch(branch) {
  return URL_TEMPLATE.replace('{BRANCH}', branch);
}

function getFileUrls(baseUrl) {
  return {
    csv: `${baseUrl}/${BENCH_CSV_FILE}`,
    json: `${baseUrl}/${COST_MODEL_FILE}`
  };
}

// Load settings from localStorage (URL param takes precedence)
function loadSettings() {
  const urlBranch = getBranchFromUrl();
  // `?csv=...&json=...` point the page at explicit files and win over what the browser
  // remembers.
  const params = new URLSearchParams(window.location.search);
  const urlCsv = params.get('csv');
  const urlJson = params.get('json');
  return {
    branch: urlBranch || localStorage.getItem(STORAGE_KEYS.BRANCH) || DEFAULT_BRANCH,
    csvUrl: (urlCsv && urlJson ? urlCsv : localStorage.getItem(STORAGE_KEYS.CSV_URL)) || '',
    jsonUrl: (urlCsv && urlJson ? urlJson : localStorage.getItem(STORAGE_KEYS.JSON_URL)) || '',
    collapsed: localStorage.getItem(STORAGE_KEYS.DATA_SOURCE_COLLAPSED) === 'true'
  };
}

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
  const urls = getFileUrls(generateUrlFromBranch(branch));

  csvInput.value = urls.csv;
  jsonInput.value = urls.json;
}

function showError(message) {
  const container = document.getElementById('plot-container');
  // The message can contain request URLs built from the user-editable
  // data-source fields, so it goes in as text, never as HTML.
  container.innerHTML = `
    <div class="error">
      <h3>Error Loading Data</h3>
      <p></p>
    </div>
  `;
  container.querySelector('.error p').textContent = message;
}

// Fill <nav> with the standard page list; `active` is the page's slug and
// `prefix` the relative path to the site root ('..' from a page, '.' from
// the home page).
function renderNav(active, prefix = '..') {
  const nav = document.querySelector('nav');
  if (!nav) return;
  const items = [[`${prefix}/index.html`, 'Home', active === null]].concat(
    PAGES.map(([slug, name]) => [`${prefix}/${slug}/index.html`, name, slug === active]));
  nav.innerHTML = '<ul>' + items.map(([href, name, isActive]) =>
    `<li><a href="${href}"${isActive ? ' class="active"' : ''}>${name}</a></li>`).join('') + '</ul>';
}

// Fill the landing page's function list from the standard page list.  The descriptions
// carry markup, so they go in as HTML; unlike `showError` below, nothing here comes from
// a user-editable field.
function renderFunctionList() {
  const list = document.querySelector('ul.function-list');
  if (!list) return;
  list.innerHTML = PAGES.map(([slug, name, description]) =>
    `<li><a href="${slug}/index.html">${name}</a>` +
    `<p class="description">${description}</p></li>`).join('');
}

function renderFooter() {
  const footer = document.querySelector('footer');
  if (!footer) return;
  footer.innerHTML = '<p>Plutus Cost Model Visualization | ' +
    '<a href="https://github.com/IntersectMBO/plutus" target="_blank">Plutus Repository</a></p>';
}

// Fill the info-panel "Data sources" list from the shared file names.
function renderDataSources() {
  const el = document.getElementById('info-data-sources');
  if (!el) return;
  el.innerHTML = `
    <dt>Data sources:</dt>
    <dd><a href="${GITHUB_DATA_URL}/${BENCH_CSV_FILE}" target="_blank">${BENCH_CSV_FILE}</a></dd>
    <dd><a href="${GITHUB_DATA_URL}/${COST_MODEL_FILE}" target="_blank">${COST_MODEL_FILE}</a>
      ${COST_MODEL_NOTE}</dd>
  `;
}


/**
 * Wire up a builtin page.  The page supplies its identity and two callbacks;
 * everything else -- navigation, data-source controls, URL handling,
 * loading -- is shared.
 *
 * @param {Object} page
 * @param {string} page.slug            Directory name, used to highlight the nav
 * @param {string} page.functionName    Benchmark name (PascalCase, as in the CSV)
 * @param {string} page.costModelName   Cost model key (camelCase, as in the JSON)
 * @param {number} page.arity           Number of arguments, for the Nop overhead
 * @param {Function} page.render        Called with {benchmarkData, costModel,
 *                                      overhead, modelPredictions} after each load
 * @param {Function} page.setupControls Called once to wire plot-specific controls
 */
function setupCostModelPage(page) {
  async function loadAndRenderData() {
    const container = document.getElementById('plot-container');
    container.innerHTML = '<div class="loading">Loading data and generating plot...</div>';

    try {
      const csvUrl = document.getElementById('csv-url').value.trim();
      const jsonUrl = document.getElementById('json-url').value.trim();

      if (!csvUrl || !jsonUrl) {
        showError('Please provide both CSV and JSON file URLs');
        return;
      }

      const { parsedData, costModelJson, overheadMap } = await loadData(csvUrl, jsonUrl);

      const benchmarkData = filterByFunction(parsedData, page.functionName);
      if (benchmarkData.length === 0) {
        showError(`No benchmark data found for ${page.functionName}`);
        return;
      }

      const costModel = extractCostModel(costModelJson, page.costModelName);
      const overhead = overheadMap[page.arity] || 0;
      const modelPredictions =
        costModel ? generateModelPredictions(benchmarkData, costModel, overhead) : [];

      page.render({ benchmarkData, costModel, overhead, modelPredictions });
    } catch (error) {
      console.error('Error loading data:', error);
      showError(`Failed to load data. Check console for details. Error: ${error.message}`);
    }
  }

  async function init() {
    renderNav(page.slug);
    renderFooter();
    renderDataSources();

    const settings = loadSettings();

    // Collapsible sections
    const dataSourceControls = document.getElementById('data-source-controls');
    const dataSourceToggle = document.getElementById('data-source-toggle');
    if (dataSourceControls && dataSourceToggle) {
      if (settings.collapsed) {
        dataSourceControls.classList.add('collapsed');
      }
      dataSourceToggle.addEventListener('click', () => {
        const isCollapsed = dataSourceControls.classList.toggle('collapsed');
        localStorage.setItem(STORAGE_KEYS.DATA_SOURCE_COLLAPSED, isCollapsed);
      });
    }

    const plotControls = document.getElementById('plot-controls');
    const plotControlsToggle = document.getElementById('plot-controls-toggle');
    if (plotControls && plotControlsToggle) {
      if (localStorage.getItem(STORAGE_KEYS.PLOT_CONTROLS_COLLAPSED) === 'true') {
        plotControls.classList.add('collapsed');
      }
      plotControlsToggle.addEventListener('click', () => {
        const isCollapsed = plotControls.classList.toggle('collapsed');
        localStorage.setItem(STORAGE_KEYS.PLOT_CONTROLS_COLLAPSED, isCollapsed);
      });
    }

    // Data-source inputs
    const branchInput = document.getElementById('branch-name');
    const csvInput = document.getElementById('csv-url');
    const jsonInput = document.getElementById('json-url');

    branchInput.value = settings.branch;
    if (settings.csvUrl && settings.jsonUrl) {
      csvInput.value = settings.csvUrl;
      jsonInput.value = settings.jsonUrl;
    } else {
      updateUrlsFromBranch();
    }
    branchInput.addEventListener('input', updateUrlsFromBranch);

    document.getElementById('reload-data').addEventListener('click', async () => {
      const branch = branchInput.value.trim() || DEFAULT_BRANCH;
      saveSettings(branch, csvInput.value.trim(), jsonInput.value.trim());
      await loadAndRenderData();
    });

    document.getElementById('copy-link').addEventListener('click', () => {
      const branch = branchInput.value.trim() || DEFAULT_BRANCH;
      const url = new URL(window.location.href);
      url.search = '';
      url.searchParams.set('branch', branch);
      navigator.clipboard.writeText(url.toString());
      const btn = document.getElementById('copy-link');
      const original = btn.textContent;
      btn.textContent = 'Copied!';
      setTimeout(() => btn.textContent = original, 1500);
    });

    page.setupControls();

    await loadAndRenderData();
  }

  document.addEventListener('DOMContentLoaded', init);
}
