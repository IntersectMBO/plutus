# RESP:PRED

for i in {1..10}; do
    taskset -c 1 cabal bench plutus-benchmark:validation \
      --benchmark-options="--csv bench-validation-auction_1-1.csv --regress cpuTime:cycles --regress numGcs:iters --regress cycles:time --regress allocated:iters --regress cycles:iters +RTS -T -RTS auction_1-1" | tee bench-validation-auction_1-1.txt; 
done


for i in {1..10}; do
    cabal bench plutus-benchmark:validation \
      --benchmark-options="--regress cpuTime:cycles --regress cycles:time --regress cycles:iters +RTS -T -A400m -RTS auction_1-1" | tee bench-validation-auction_1-1-gc-large.txt; 
done



for i in {1..10}; do
    cabal bench plutus-benchmark:validation \
      --benchmark-options="--regress cpuTime:cycles --regress numGcs:iters --regress allocated:iters --regress cycles:time --regress cycles:iters +RTS -T -A1m -RTS auction_1-1" | tee bench-validation-auction_1-1-gc-small.txt; 
done

# DEBUG LOG
# We run it 10 times. 
# The 1st/7th/5th were severely inflated.
# So the error rate is about 30%
# One failure mode is everything becomes slower (1/7) 
# The second is everything became faster (5th) 
The only metric that changes (in addition to clock time) is cycles:iters 
We suspect is garbage collection... but we are not allocating more so it should not be the case.
# We run again with a large amount of nursery (added -rtsopts to the bench) -- with -A400m (first gen nursery)
benchmarking auction_1-1 
*** Error: no data available for "numGcs"
validation: Prelude.undefined
So we removed "--regress numGcs:iters --regress allocated:iters"

With more memory -A we get worse results

Then we run a 10 batch of auction_1-1 pinned to core 0,1,7 (see results)



run_on_core() {
  core="$1"
  taskset -c $core cabal bench plutus-benchmark:validation \
    --benchmark-options="--csv bench-validation-auction_1-1.csv --regress cpuTime:cycles --regress numGcs:iters --regress cycles:time --regress allocated:iters --regress cycles:iters +RTS -T -RTS auction_1-1" | tee bench-validation-auction_1-1.txt; 
}

sometimes the cpu cores do not get up to speed.
either set every core to performance or pin the core
or slow down a core and see if the results are consistent

https://stackoverflow.com/questions/4713088/how-do-i-use-git-bisect
https://www.kernel.org/doc/Documentation/cpu-freq/governors.txt
https://wiki.archlinux.org/title/CPU_frequency_scaling#Scaling_governors

non pessimised code: 

https://haskell.foundation/hs-opt-handbook.github.io/src/Measurement_Observation/Core_Profiling/data_type_memory_footprint.html#memory-footprint-of-data-types-chapter

https://youtu.be/IroPQ150F6c?si=jJL3cDMLw55OPf84