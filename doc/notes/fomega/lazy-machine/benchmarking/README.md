This directory contains a number of test cases and scripts to run them
on various Plutus Core evaluators and plot the results using R.  The
scripts are hacked together and may not be very robust.  You may have trouble
if you're not using Linux.

To run the benchmarks and plot the results, you'll need:

 * The `gpp` preprocessor
 * The GNU time command. This should be in /usr/bin/time on Linux, but apparently doesn't come as standard on OSX.  If it's in some other location, change the variable TIME in each of the run-xxx scripts.
 * R.

To run all of the tests, type `run-all`.  This will run each of the other run-xxx scripts and save
the results in files in this directory.  The scripts assume that the `plc` command is somewhere 
in your path.  If not, change the `plc` variable in each run-xxx script to point to the correct location.

The tests may take some time (an hour or more) and may run into
problems if memory is limited. They ran successfully on an 8GB machine
with browsers and other memory-hungry programs shut down to maximise free
memory.

To plot the results, start R and type `source ("r/draw-all")` at the command prompt.
This should produce several PDFs.  The R scripts are not foolproof: they were written
based on the intial set of results so that the most time-consuming results could be 
plotted first to get the scale right, and may require some modification if the
test results change significantly.



