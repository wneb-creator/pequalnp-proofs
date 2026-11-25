"""Seven-bit singleton relaxation of shared neighborhood-OR synthesis."""
import argparse
import itertools
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
SOLVER = Path('/tmp/oec/pequalnp-pilot-103/setup/lean-4.36.0-linux/bin/cadical')
TARGETS = [sum(1 << (h-7) for h in hs) for hs in
           [[8,10],[7,9,13],[8,13],[7,11,12],[10,11,13],[9,10,12],[8,9,11]]]


class CNF:
    def __init__(self): self.n=0; self.clauses=[]
    def var(self): self.n+=1; return self.n
    def add(self,*xs): self.clauses.append(list(xs))
    def exactly_one(self,xs):
        self.add(*xs)
        previous=None
        for x in xs:
            current=self.var()
            self.add(-x,current)
            if previous is not None:
                self.add(-previous,current)
                self.add(-x,-previous)
            previous=current


def build(k,pin=False,exact=False):
    f=CNF()
    rows=[1<<i for i in range(7)]
    if exact: rows += [127^target for target in TARGETS]
    bits=[[f.var() for _ in rows] for _ in range(7+k)]
    for i in range(7):
        for b,row in enumerate(rows): f.add(bits[i][b] if row>>i&1 else -bits[i][b])
    choices=[]
    baseline=[]
    nextwire=7
    for target in TARGETS:
        sources=[b for b in range(7) if target>>b&1]
        a=sources[0]
        for b in sources[1:]:
            baseline.append(('or',a,b))
            a=nextwire; nextwire+=1
    if pin: assert k==len(baseline)
    for g in range(k):
        options={}
        z=bits[7+g]
        for a,b in itertools.combinations(range(7+g),2):
            for op in ['and','or']:
                s=f.var();options[(op,a,b)]=s
                for j in range(len(rows)):
                    x,y=bits[a][j],bits[b][j]
                    if op=='and':
                        f.add(-s,-x,-y,z[j]);f.add(-s,x,-z[j]);f.add(-s,y,-z[j])
                    else:
                        f.add(-s,x,y,-z[j]);f.add(-s,-x,z[j]);f.add(-s,-y,z[j])
        f.exactly_one(list(options.values()))
        if pin:
            op,a,b=baseline[g]
            f.add(options[(op,min(a,b),max(a,b))])
        choices.append(options)
    matches=[]
    for target in TARGETS:
        ms=[]
        for g in range(k):
            m=f.var();ms.append(m)
            for b,row in enumerate(rows): f.add(-m,bits[7+g][b] if target&row else -bits[7+g][b])
        f.add(*ms);matches.append(ms)
    return f,choices,matches


def evaluate(gates):
    values=[sum(1<<row for row in range(128) if row>>i&1) for i in range(7)]
    sets=[1<<i for i in range(7)]
    for op,a,b in gates:
        values.append(values[a]&values[b] if op=='and' else values[a]|values[b])
        sets.append(sets[a]&sets[b] if op=='and' else sets[a]|sets[b])
    targets=[sum(1<<row for row in range(128) if row&t) for t in TARGETS]
    return {'singleton_targets_present':all(t in sets for t in TARGETS),
            'full_targets_present':all(t in values for t in targets),
            'sets':sets,
            'full_output_wires':[values.index(t) if t in values else None for t in targets]}


def main():
    p=argparse.ArgumentParser();p.add_argument('--gates',type=int,default=11)
    p.add_argument('--seconds',type=int,default=30);p.add_argument('--pin',action='store_true')
    p.add_argument('--exact',action='store_true')
    args=p.parse_args();f,choices,matches=build(args.gates,args.pin,args.exact)
    name=f'multioutput-{args.gates}'+('-pinned' if args.pin else '')+('-exact' if args.exact else '')
    cnf=ROOT/(name+'.cnf')
    with cnf.open('w') as h:
        h.write(f'p cnf {f.n} {len(f.clauses)}\n')
        for c in f.clauses:h.write(' '.join(map(str,c))+' 0\n')
    log=ROOT/(name+'.stdout')
    with log.open('w') as h:
        result=subprocess.run([str(SOLVER),'-t',str(args.seconds),str(cnf)],stdout=h,stderr=subprocess.STDOUT)
    report={'gates':args.gates,'pinned':args.pin,'variables':f.n,'clauses':len(f.clauses),
            'exit':result.returncode,'semantics':'exact14row OR functions' if args.exact else 'singleton-only union/intersection relaxation'}
    if result.returncode==10:
        model={int(v) for line in log.read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)>0}
        gates=[next(c for c,v in options.items() if v in model) for options in choices]
        report['circuit']=gates;report['validation']=evaluate(gates)
    (ROOT/(name+'.json')).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__=='__main__':main()
