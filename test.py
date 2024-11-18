# while true; do cabal bench plutus-benchmark:bitwise-bench --benchmark-options="--regress cpuTime:iters --regress allocated:iters --regress cpuTime:cycles --regress cpuTime:cycles --regress cycles:iters --regress gcCpuSeconds:iters --regress mutatorCpuSeconds:iters +RTS -T" >> bitwise-bench.txt ; done 
# while true; do cabal bench plutus-benchmark:bitwise-bench --benchmark-options="--regress cycles:cpuTime +RTS -A64m" >> bitwise-bench-2.txt ; done 
# while true; do cabal bench plutus-benchmark:validation-decode --benchmark-options="--regress cpuTime:iters --regress allocated:iters --regress cpuTime:cycles --regress cycles:iters --regress gcCpuSeconds:iters --regress mutatorCpuSeconds:iters +RTS -T" >> validation-decode.txt ; done 

import sys 


data = {
    'cpuTime:iters': [],
    'allocated:iters': [],
    'cpuTime:cycles': [],
    'cycles:iters': [],
    'cycles:cpuTime': [],
    'gcCpuSeconds:iters': [],
    'mutatorCpuSeconds:iters': [],
}

with open(sys.argv[1]) as f:
    lines = f.readlines()
    responder = ''
    predictor = ''
    i = 0 
    while i < len(lines):
        line = lines[i]
        i += 1
        if 'cpuTime:' in line:
            responder = 'cpuTime'
        elif 'allocated:' in line:
            responder = 'allocated'
        elif 'cycles:' in line:
            responder = 'cycles'
        elif 'gcCpuSeconds:' in line:
            responder = 'gcCpuSeconds'
        elif 'mutatorCpuSeconds:' in line:
            responder = 'mutatorCpuSeconds'
        else:
            continue
        predictor, value, *_ = lines[i].split()
        i += 2
        regression = f"{responder}:{predictor}"
        data[regression].append(float(value))
    
    for regression, values in data.items():
        if not values:
            continue
        minv = min(values)
        maxv = max(values)
        percentage_change = ((maxv - minv) / minv) * 100
        print(f"{regression}, {len(values)} samples, min {minv}, max {maxv}, {percentage_change:.2f}%")


# min=$(grep "cpuTime " bitwise-bench.txt | awk '{print $2}' | sort -n | head -n 1)
# max=$(grep "cpuTime " bitwise-bench.txt | awk '{print $2}' | sort -n | tail -n 1)
# echo $min $max
# percentage_change=$(echo "scale=2; (($max - $min) / $min) * 100" | bc)
