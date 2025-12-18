const FUNCTION_NAME = "ScaleValue";
const COST_MODEL_NAME = "scaleValue";
const ARITY = 2;

function layout({ yRangeMode }) {
  return {
    title: `${FUNCTION_NAME}: runtime vs Value size (arg2)`,
    xaxis: { title: "Value size metric (arg2)", zeroline: true },
    yaxis: { title: "Runtime (ps)", rangemode: yRangeMode, zeroline: true },
    hovermode: "closest",
    legend: { orientation: "h" },
    margin: { t: 60, r: 30, b: 60, l: 70 },
  };
}

function buildScatter(data, overhead) {
  return {
    x: data.map((row) => row.args[1]),
    y: data.map((row) => row.time),
    mode: "markers",
    type: "scatter",
    name: "Benchmark data",
    marker: { color: "#1f77b4", size: 7, opacity: 0.75 },
    hovertemplate: "Value size=%{x}<br>time=%{y:.2f} ps<extra></extra>",
  };
}

function buildModelCurve(data, model) {
  const xValues = Array.from(new Set(data.map((row) => row.args[1]))).sort((a, b) => a - b);
  const yValues = xValues.map((x) => model([0, x]));
  return {
    x: xValues,
    y: yValues,
    mode: "lines",
    type: "scatter",
    name: "Model prediction",
    line: { color: "#d62728", width: 2 },
    hovertemplate: "Value size=%{x}<br>model=%{y:.2f} ps<extra></extra>",
  };
}

async function loadAndPlot() {
  showLoading();

  const { csvUrl, jsonUrl } = readDataSourceInputs();
  updateLinkWithParams({ csvUrl, jsonUrl });

  const [csvData, costModel] = await loadData(csvUrl, jsonUrl);
  const benchRows = filterByFunction(csvData, FUNCTION_NAME, ARITY);

  if (benchRows.length === 0) {
    showError("No benchmark data found for ScaleValue with arity 2.");
    return;
  }

  const overhead = computeOverhead(benchRows);
  const modelDef = costModel[COST_MODEL_NAME];
  if (!modelDef) {
    showError(`Cost model '${COST_MODEL_NAME}' not found in JSON file.`);
    return;
  }

  const model = buildModelEvaluator(modelDef, overhead);
  const scatter = buildScatter(benchRows, overhead);
  const modelCurve = buildModelCurve(benchRows, model);

  const yRangeMode = document.getElementById("y-axis-mode").value === "zero" ? "tozero" : "normal";
  const traces = [scatter];
  if (document.getElementById("show-model").checked) {
    traces.push(modelCurve);
  }

  Plotly.newPlot("plot-container", traces, layout({ yRangeMode }), { responsive: true });
  populateInfoPanel({ data: benchRows, modelDef, overhead });
}

function populateInfoPanel({ data, modelDef, overhead }) {
  const xs = data.map((row) => row.args[1]);
  const ys = data.map((row) => row.time);
  document.getElementById("info-data-points").textContent = data.length;
  document.getElementById("info-x-range").textContent = `${Math.min(...xs)} to ${Math.max(...xs)}`;
  document.getElementById("info-time-range").textContent = `${Math.min(...ys).toFixed(2)} to ${Math.max(...ys).toFixed(2)} ps`;
  document.getElementById("info-model-type").textContent = modelDef.modelType || "-";
  document.getElementById("info-model-formula").textContent = modelDef.model || "-";
  document.getElementById("info-overhead").textContent = overhead.toFixed(2);
}

function wireControls() {
  document.getElementById("reload-data").addEventListener("click", loadAndPlot);
  document.getElementById("show-model").addEventListener("change", loadAndPlot);
  document.getElementById("y-axis-mode").addEventListener("change", loadAndPlot);

  setupDataSourceInputs({
    onChange: loadAndPlot,
    defaults: getDefaultDataSources({ branch: "master" }),
  });

  setupCollapsibleSections();
  setupCopyLinkButton();
}

wireControls();
loadAndPlot();
