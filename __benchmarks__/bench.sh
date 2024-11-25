# RESP:PRED

for i in {1..30}; do
    cabal bench plutus-benchmark:validation \
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

On Monday run the benchmark with -rtsopts and -S, outside cabal and criterion 

jeff has no meeting until thristda