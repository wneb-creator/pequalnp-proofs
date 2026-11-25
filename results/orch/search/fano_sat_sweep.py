#!/usr/bin/env python3
import importlib.util
import json
import subprocess
import sys
import time
from pathlib import Path
from types import SimpleNamespace

base = Path('/tmp/oec/pequalnp-pilot-147')
spec = importlib.util.spec_from_file_location('fano_sat', base/'fano_sat.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
data = json.loads((base/'fano-tests.json').read_text())
out = base/'fano-sat-sweep'
out.mkdir(exist_ok=True)
canonical = mod.canonical(data)
summary = []
seconds = int(sys.argv[1]) if len(sys.argv) > 1 else 60

for span in [2, 3, 4]:
    for first in range(0, 7-span+1):
        deleted = 3*first+1
        gates = mod.delete_gate(data, canonical, deleted, 'a')
        # Free a contiguous group of stars and each OR gate involving it,
        # preserving all other gates of the known 27-gate circuit.
        old_free = set(range(3*first,3*(first+span)))
        old_free.update(20+j for j in range(max(1,first),min(6,first+span-1)+1))
        free = sorted(g-(g>deleted) for g in old_free if g != deleted)
        name = f'span{span}-first{first}'
        fixed = out/(name+'.fixed.json')
        fixed.write_text(json.dumps(gates))
        cnf = out/(name+'.cnf')
        args = SimpleNamespace(tests=str(base/'fano-tests.json'), gates=26,
            output=str(cnf), first=None, fixed=str(fixed),
            free=','.join(map(str,free)), and_count=None, irredundant=False)
        start=time.monotonic()
        mod.encode(args)
        with (out/(name+'.stdout')).open('w') as stdout, (out/(name+'.stderr')).open('w') as stderr:
            result=subprocess.run([str(base/'cadical/build/cadical'),'-t',str(seconds),str(cnf)],stdout=stdout,stderr=stderr)
        record={'name':name,'deleted':deleted,'free':free,'exit':result.returncode,'seconds':time.monotonic()-start}
        summary.append(record)
        (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
        print(json.dumps(record),flush=True)
        if result.returncode == 10:
            mod.decode(SimpleNamespace(meta=str(cnf)+'.json',model=str(out/(name+'.stdout')),output=str(out/(name+'.witness.json'))))
            print('FOUND WITNESS',flush=True)
            sys.exit(0)
        # The DIMACS instance can be regenerated exactly from fixed+free.
        cnf.unlink()
print('DONE SCOPED SWEEP',flush=True)
