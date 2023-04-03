import json 
import os 

result = []

for benchmark in os.getenv("BENCHMARKS").split():
    with open(f"{benchmark}-output.txt", "r") as file:
        name = ""
        for line in file.readlines():
            if line.startswith("benchmarking"):
                name = line.split()[1]
            elif line.startswith("mean"):
                parts = line.split()
                mean = float(parts[1])
                unit = parts[2]
                if unit == "ms":
                    mean = mean * 1000
                    unit = "μs"
                result.append({
                    "name": f"{benchmark}-{name}",
                    "unit": unit,
                    "value": mean
                })

with open("output.json", "w") as file: 
  json.dump(result, file)