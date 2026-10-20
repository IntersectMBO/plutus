#!/usr/bin/env python3
"""Adjacent paired measurements using two sequential, persistent CEK processes."""
import argparse
import csv
import gzip
import hashlib
import json
import os
import pathlib
import random
import select
import subprocess
import threading
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = HERE.parent/'results'/'comprehensive'
BIN = HERE/'bin'/'comprehensive'
VARIANTS = ['baseline', 'ra-erased-context']
ENV = dict(os.environ, plutus_benchmark_datadir=str(ROOT/'plutus-benchmark'))

parser = argparse.ArgumentParser()
parser.add_argument('mode', choices=['check', 'paired', 'canonical'])
parser.add_argument('--rounds', type=int, default=10)
parser.add_argument('--seconds', type=float, default=.075)
parser.add_argument('--cpu', type=int, default=15)
parser.add_argument('--prefix', default='paired')
parser.add_argument('--nursery', help='Optional RTS allocation area, e.g. 4m, for a separately labeled GC experiment')
parser.add_argument('--only', nargs='*', help='Optional exact catalog names for targeted confirmation')
a = parser.parse_args()
if a.mode != 'paired' and (a.only or a.nursery):
    parser.error('--only and --nursery apply only to paired measurements')
OUT.mkdir(exist_ok=True)

def catalog(variant):
    raw = subprocess.check_output([str(BIN/f'server-{variant}'), 'catalog', str(ROOT/'plutus-benchmark')], env=ENV, text=True)
    return [dict(index=int(i), suite=suite, name=name) for i,suite,name in
            (line.split('\t') for line in raw.splitlines())]

def read_line(proc):
    ready,_,_ = select.select([proc.stdout], [], [], 300)
    if not ready:
        raise RuntimeError('Benchmark server timed out after 300 seconds')
    line = proc.stdout.readline().rstrip('\n')
    if not line:
        raise RuntimeError(f'Benchmark server exited: {proc.poll()}')
    return line

class Server:
    def __init__(self, variant, tag=''):
        self.err = (HERE/'logs'/f'{a.prefix}-{a.mode}-{variant}{tag}.stderr').open('w')
        self.cmd = ['taskset','-c',str(a.cpu),str(BIN/f'server-{variant}'), 'server',
                    str(ROOT/'plutus-benchmark'), '+RTS','-N1','-T','-s','-K512M']
        if a.nursery: self.cmd.append('-A'+a.nursery)
        self.cmd.append('-RTS')
        self.proc = subprocess.Popen(self.cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=self.err, text=True, bufsize=1, env=ENV)
        assert read_line(self.proc) == 'ready\t327'

    def ask(self, command):
        self.proc.stdin.write(command+'\n')
        self.proc.stdin.flush()
        return read_line(self.proc)

    def checked(self, command):
        result = self.ask(command)
        if result.startswith('error\t'):
            raise RuntimeError(f'{command}: {result}')
        return result

    def close(self):
        if self.proc.poll() is None:
            self.proc.stdin.close()
            try:
                self.proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                self.proc.terminate()
                self.proc.wait(timeout=10)
        self.err.close()

def telemetry(stop):
    with (OUT/f'{a.prefix}-{a.mode}-host.jsonl').open('w') as out:
        while not stop.is_set():
            snapshot = dict(time=time.time(), loadavg=pathlib.Path('/proc/loadavg').read_text().strip())
            stat = pathlib.Path('/proc/stat').read_text().splitlines()
            snapshot['cpu_ticks'] = {line.split()[0]:list(map(int,line.split()[1:]))
                for line in stat if line.split()[0] in ['cpu',f'cpu{a.cpu}',f'cpu{a.cpu+16}']}
            snapshot['frequency_khz'] = {str(i):pathlib.Path(f'/sys/devices/system/cpu/cpu{i}/cpufreq/scaling_cur_freq').read_text().strip()
                                         for i in [a.cpu,a.cpu+16]}
            out.write(json.dumps(snapshot)+'\n'); out.flush()
            stop.wait(2)

specs = catalog('baseline')
assert specs == catalog('ra-erased-context')
assert len(specs) == 327
if a.only:
    specs = [s for s in specs if s['name'] in a.only]
    assert len(specs) == len(a.only)
if a.mode == 'check':
    (OUT/'catalog.json').write_text(json.dumps(specs,indent=2)+'\n')
    manifests = []
    for folder, pattern in [('validation/data','*.flat'),('force-delay/data','*.flat'),('marlowe/scripts','*')]:
        for f in sorted((ROOT/'plutus-benchmark'/folder).rglob(pattern)):
            if f.is_file() and f.suffix in ['.flat','.benchmark']:
                if folder == 'marlowe/scripts' and f.suffix == '.flat' and f.name != 'sop.flat':
                    continue
                manifests.append(dict(path=str(f.relative_to(ROOT)), bytes=f.stat().st_size,
                                      sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
    (OUT/'inputs.json').write_text(json.dumps(manifests,indent=2)+'\n')
    binaries = {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(BIN.iterdir()) if p.is_file()}
    (OUT/'binaries.json').write_text(json.dumps(binaries,indent=2)+'\n')

servers = {}
stop = threading.Event()
monitor = threading.Thread(target=telemetry,args=(stop,),daemon=True)
monitor.start()
(OUT/f'{a.prefix}-{a.mode}-invocation.json').write_text(json.dumps(
    dict(arguments=vars(a), started=time.time(), data_root=ENV['plutus_benchmark_datadir']),indent=2)+'\n')
try:
    if a.mode == 'check':
        for v in VARIANTS:
            servers[v] = Server(v)
    if a.mode == 'check':
        results = []
        with gzip.open(OUT/'correctness-baseline.tsv.gz','wt') as expected:
            for n,s in enumerate(specs):
                replies = [servers[v].checked(f'check {s["index"]}') for v in VARIANTS]
                assert replies[0] == replies[1], s['name']
                expected.write(s['name']+'\t'+replies[0]+'\n')
                row = dict(**s, result_budget_log_sha256=hashlib.sha256(replies[0].encode()).hexdigest())
                if s['suite']=='validation':
                    full = [servers[v].ask(f'full-check {s["index"]}') for v in VARIANTS]
                    assert full[0] == full[1], (s['name'],full)
                    row['full_status']='ok' if full[0].startswith('ok\t') else full[0]
                    row['full_budget_log_sha256']=hashlib.sha256(full[0].encode()).hexdigest()
                    expected.write(s['name']+'/full\t'+full[0]+'\n')
                results.append(row)
                if n%25==0: print(f'Checked {n+1}/{len(specs)}: {s["name"]}',flush=True)
        (OUT/'correctness.json').write_text(json.dumps(results,indent=2)+'\n')
        print(f'PASS: {len(specs)} exact result/budget/log comparisons',flush=True)
    elif a.mode == 'paired':
        checked = {r['index']:r for r in json.loads((OUT/'correctness.json').read_text())}
        work = [(s,'cek') for s in specs] + [(s,'full') for s in specs
            if s['suite']=='validation' and checked[s['index']]['full_status']=='ok']
        fields = ['round','index','suite','name','mode','variant','order','timestamp','reps',
                  'seconds','cpu_seconds','allocated_bytes','gc_cpu_seconds','gc_wall_seconds','gcs']
        with (OUT/f'{a.prefix}.csv').open('w') as f:
            writer=csv.DictWriter(f,fieldnames=fields,lineterminator='\n'); writer.writeheader()
            for r in range(a.rounds):
                for server in servers.values(): server.close()
                servers = {}
                for v in VARIANTS:
                    servers[v] = Server(v, f'-r{r+1}')
                order = list(work)
                random.Random(9271+r).shuffle(order)
                for j,(s,mode) in enumerate(order):
                    vs = VARIANTS if (r+s['index']+(mode=='full'))%2==0 else VARIANTS[::-1]
                    reps = max(int(servers[v].checked(f'calibrate {s["index"]} {mode} {a.seconds}')) for v in vs)
                    for position,v in enumerate(vs):
                        timestamp = time.time()
                        values=servers[v].checked(f'sample {s["index"]} {mode} {reps}').split('\t')
                        assert len(values)==7
                        row=dict(round=r+1,**s,mode=mode,variant=v,order=position,timestamp=timestamp)
                        row.update(zip(fields[8:],values));writer.writerow(row);f.flush()
                    if (j+1)%25==0 or j+1==len(order):
                        print(f'Round {r+1}/{a.rounds}: {j+1}/{len(order)} paired workloads',flush=True)
    else:
        commands = []
        for r in range(a.rounds):
            targets = ['validation','validation-full','marlowe','nofib','force-delay']
            targets = targets[r%len(targets):]+targets[:r%len(targets)]
            for target in targets:
                vs = VARIANTS if r%2==0 else VARIANTS[::-1]
                for v in vs:
                    stem=f'canonical-{target}-{v}-r{r+1}'
                    cmd=['taskset','-c',str(a.cpu),str(BIN/f'{target}-{v}'),'-L',str(a.seconds),
                         '--resamples','1000','--csv',str(OUT/f'{stem}.csv'),
                         '-o',str(HERE/'logs'/f'{stem}.html')]
                    print(stem,flush=True);start=time.time()
                    with (OUT/f'{stem}.log').open('w') as log:
                        completed=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,env=ENV,cwd=ROOT)
                    commands.append(dict(command=cmd,elapsed=time.time()-start,exit_code=completed.returncode))
                    (OUT/'canonical-commands.json').write_text(json.dumps(commands,indent=2)+'\n')
                    completed.check_returncode()
finally:
    for server in servers.values(): server.close()
    stop.set(); monitor.join(timeout=3)
