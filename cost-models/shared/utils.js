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
 * Extract cost model from builtinCostModelC.json for a specific function
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

    if (!csvResponse.ok) {
      throw new Error(`Failed to load CSV: ${csvResponse.statusText}`);
    }

    if (!jsonResponse.ok) {
      throw new Error(`Failed to load JSON: ${jsonResponse.statusText}`);
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
