<!doctype html>
<html>
<head>
  <meta charset="utf-8"/>
  <title>criterion report</title>
  <script>
    {{{js-chart}}}
    {{{js-criterion}}}
  </script>
  <style>
    {{{criterion-css}}}
  </style>
  <script type="application/json" id="report-data">
    {{{json}}}
  </script>
  <meta name="viewport" content="width=device-width, initial-scale=1">
</head>
<body>
  <div class="content">
    <h1 class='title'>criterion performance measurements</h1>
    <p class="no-print"><a href="#grokularation">want to understand this report?</a></p>
    <h1 id="overview"><a href="#overview">overview</a></h1>
    <div class="no-print">
      <select id="sort-overview" class="select">
        <option value="report-index">index</option>
        <option value="lex">lexical</option>
        <option value="colex">colexical</option>
        <option value="duration">time ascending</option>
        <option value="rev-duration">time descending</option>
      </select>
      <span class="overview-info">
        <a href="#controls-explanation" class="info" title="click bar/label to zoom; x-axis to toggle logarithmic scale; background to reset">&#9432;</a>
        <a id="legend-toggle" class="chevron button"></a>
      </span>
    </div>
    <aside id="overview-chart"></aside>
    <main id="reports"></main>
  </div>

  <aside id="controls-explanation" class="explanation no-print">
    <h1><a href="#controls-explanation">controls</a></h1>

    <p>
      The overview chart can be controlled by clicking the following elements:
      <ul>
        <li><em>a bar or its label</em> zooms the x-axis to that bar</li>
        <li><em>the background</em> resets zoom to the entire chart</li>
        <li><em>the x-axis</em> toggles between linear and logarithmic scale</li>
        <li><em>the chevron</em> in the top-right toggles the the legend</li>
        <li><em>a group name in the legend</em> shows/hides that group</li>
      </ul>
    </p>

    <p>
      The overview chart supports the following sort orders:
      <ul>
        <li><em>index</em> order is the order as the benchmarks are defined in criterion</li>
        <li><em>lexical</em> order sorts <a href="https://en.wikipedia.org/wiki/Lexicographic_order#Motivation_and_definition">groups left-to-right</a>, alphabetically</li>
        <li><em>colexical</em> order sorts <a href="https://en.wikipedia.org/wiki/Lexicographic_order#Colexicographic_order">groups right-to-left</a>, alphabetically</li>
        <li><em>time ascending/descending</em> order sorts by the estimated mean execution time</li>
      </ul>
    </p>

  </aside>

  <aside id="grokularation" class="explanation">

    <h1><a>understanding this report</a></h1>

    <p>
      In this report, each function benchmarked by criterion is assigned a section of its own.
      <span class="no-print">The charts in each section are active; if you hover your mouse over data points and annotations, you will see more details.</span>
    </p>

    <ul>
      <li>
        The chart on the left is a <a href="http://en.wikipedia.org/wiki/Kernel_density_estimation">kernel density estimate</a> (also known as a KDE) of time measurements.
        This graphs the probability of any given time measurement occurring.
        A spike indicates that a measurement of a particular time occurred; its height indicates how often that measurement was repeated.
      </li>

      <li>
        The chart on the right is the raw data from which the kernel density estimate is built.
        The <em>x</em>-axis indicates the number of loop iterations, while the <em>y</em>-axis shows measured execution time for the given number of loop iterations.
        The line behind the values is the linear regression estimate of execution time for a given number of iterations.
        Ideally, all measurements will be on (or very near) this line.
        The transparent area behind it shows the confidence interval for the execution time estimate.
      </li>
    </ul>

    <p>
      Under the charts is a small table.
      The first two rows are the results of a linear regression run on the measurements displayed in the right-hand chart.
    </p>

    <ul>
      <li>
        <em>OLS regression</em> indicates the time estimated for a single loop iteration using an ordinary least-squares regression model.
        This number is more accurate than the <em>mean</em> estimate below it, as it more effectively eliminates measurement overhead and other constant factors.
      </li>
      <li>
        <em>R<sup>2</sup>; goodness-of-fit</em> is a measure of how accurately the linear regression model fits the observed measurements.
        If the measurements are not too noisy, R<sup>2</sup>; should lie between 0.99 and 1, indicating an excellent fit.
        If the number is below 0.99, something is confounding the accuracy of the linear model.
      </li>
      <li>
        <em>Mean execution time</em> and <em>standard deviation</em> are statistics calculated from execution time divided by number of iterations.
      </li>
    </ul>

    <p>
      We use a statistical technique called the <a href="http://en.wikipedia.org/wiki/Bootstrapping_(statistics)">bootstrap</a> to provide confidence intervals on our estimates.
      The bootstrap-derived upper and lower bounds on estimates let you see how accurate we believe those estimates to be.
      <span class="no-print">(Hover the mouse over the table headers to see the confidence levels.)</span>
    </p>

    <p>
      A noisy benchmarking environment can cause some or many measurements to fall far from the mean.
      These outlying measurements can have a significant inflationary effect on the estimate of the standard deviation.
      We calculate and display an estimate of the extent to which the standard deviation has been inflated by outliers.
    </p>

  </aside>

  <footer>
    <div class="content">
      <h1 class="colophon-header">colophon</h1>
      <p>
        This report was created using the <a href="http://hackage.haskell.org/package/criterion">criterion</a>
        benchmark execution and performance analysis tool.
      </p>
      <p>
        Criterion is developed and maintained
        by <a href="http://www.serpentine.com/blog/">Bryan O'Sullivan</a>.
      </p>
    </div>
  </footer>
</body>
</html>
