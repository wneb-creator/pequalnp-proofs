"""Bounded serial QQ trace run, with an input companion for independent replay."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import time

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('input');p.add_argument('prefix')
p.add_argument('--seconds',type=int,default=30)
p.add_argument('--memory-mib',type=int,default=1024)
p.add_argument('--pairs',type=int,default=0)
a=p.parse_args();source=Path(a.input);prefix=Path(a.prefix)
base=Path(__file__).parent
tokens=source.read_text().split();position=0
def take():
    global position
    value=int(tokens[position]);position+=1;return value
n,m,characteristic,total=take(),take(),take(),take()
assert characteristic==0 and n>0 and m>0
lengths=[take() for _ in range(m)];assert sum(lengths)==total
names=['x'+str(i) for i in range(n)];polynomials=[]
for length in lengths:
    terms=[]
    for _ in range(length):
        numerator,denominator=take(),take();coeff=Fraction(numerator,denominator)
        exponents=[take() for _ in range(n)]
        assert coeff and min(exponents)>=0
        term=str(coeff)+''.join('*'+name+('^'+str(e) if e!=1 else '')
            for name,e in zip(names,exponents) if e)
        if terms and coeff>0:term='+'+term
        terms.append(term)
    polynomials.append(''.join(terms))
assert position==len(tokens)
companion=prefix.with_suffix('.f4.in')
companion.write_text('0 '+str(n)+' '+str(m)+'\n'+' '.join(names)+'\n'+'\n'.join(polynomials)+'\n')
binary=base/'certificate-trace/neogb_cli_trace'
def limits():
    memory=a.memory_mib*1024**2
    resource.setrlimit(resource.RLIMIT_AS,(memory,memory))
    resource.setrlimit(resource.RLIMIT_CORE,(0,0))
start=time.monotonic()
with prefix.with_suffix('.log').open('w') as out:
    try:
        r=subprocess.run([str(binary),str(source),str(prefix.with_suffix('.basis.json')),
                          str(prefix.with_suffix('.trace')),str(a.pairs)],
                         stdout=out,stderr=subprocess.STDOUT,preexec_fn=limits,timeout=a.seconds)
        result={'status':'COMPLETED' if r.returncode==0 else 'FAILED_NO_VERDICT','returncode':r.returncode}
    except subprocess.TimeoutExpired:
        result={'status':'UNKNOWN_TIME_LIMIT'}
result.update({'wall_seconds':time.monotonic()-start,'seconds_limit':a.seconds,
    'memory_mib_limit':a.memory_mib,'pairs':a.pairs,'input':str(source),
    'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'companion_sha256':hashlib.sha256(companion.read_bytes()).hexdigest(),
    'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest()})
prefix.with_suffix('.run.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
