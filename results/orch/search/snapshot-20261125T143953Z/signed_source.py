#!/usr/bin/env python3
"""Petersen AND/OR synthesis with shared signed sources. Counterexample search only."""
import argparse
import itertools
import json
import shutil
from pathlib import Path

EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
N = 10

def target(row):
    return any((row >> u) & 1 and (row >> v) & 1 for u, v in EDGES)

def rows_for(mode, extra):
    if mode == 'all': return list(range(1 << N))
    edges = {sum(1 << v for v in e) for e in EDGES}
    maximal = {r for r in range(1 << N) if not target(r) and all(target(r | (1 << v)) for v in range(N) if not (r >> v) & 1)}
    selected = edges | maximal | {0, (1 << N)-1}
    selected |= {1 << v for v in range(N)}
    selected |= {((1 << N)-1) ^ (1 << v) for v in range(N)}
    selected |= {int(r) for r in extra.split(',') if r}
    assert all(0 <= r < (1 << N) for r in selected)
    return sorted(selected)

class CNF:
    def __init__(self, path):
        self.path = path
        self.body = path.with_suffix(path.suffix + '.body')
        self.file = self.body.open('w')
        self.variables = self.clauses = 0
    def fresh(self):
        self.variables += 1
        return self.variables
    def add(self, literals):
        self.clauses += 1
        self.file.write(' '.join(map(str, literals)) + ' 0\n')
    def one(self, variables):
        self.add(variables)
        for a, b in itertools.combinations(variables, 2): self.add([-a, -b])
    def xor(self, out, a, b):
        for clause in ([a,b,-out],[-a,-b,-out],[a,-b,out],[-a,b,out]): self.add(clause)
    def finish(self):
        self.file.close()
        with self.path.open('w') as out, self.body.open() as body:
            out.write(f'p cnf {self.variables} {self.clauses}\n')
            shutil.copyfileobj(body, out)
        self.body.unlink()

def generate(args):
    m, k = args.gates, args.not_count
    assert m >= 1 and (args.unrestricted_negation or 0 <= k <= 4)
    rows = rows_for(args.rows, args.extra_rows)
    if args.essential_mask is not None:
        assert k == 1 and not args.unrestricted_negation and 0 <= args.essential_mask < (1 << N)
        rows = sorted(set(rows) | {0,3,1023,args.essential_mask})
    path = Path(args.out)
    path.parent.mkdir(parents=True, exist_ok=True)
    cnf = CNF(path)
    marks = [cnf.fresh() for _ in range(N + 1 + m)]
    if args.unrestricted_negation:
        for marked in marks: cnf.add([marked])
    else:
        for chosen in itertools.combinations(marks, k + 1): cnf.add([-v for v in chosen])
        if k:
            for chosen in itertools.combinations(marks, len(marks)-k+1): cnf.add(list(chosen))
    gates = []
    for j in range(m):
        available = N + 1 + j
        gate = {'or':cnf.fresh(), 'sign':[cnf.fresh(),cnf.fresh()], 'select':[[cnf.fresh() for _ in range(available)] for _ in range(2)]}
        gates.append(gate)
        for slot in range(2):
            cnf.one(gate['select'][slot])
            for source, selected in enumerate(gate['select'][slot]): cnf.add([-selected,-gate['sign'][slot],marks[source]])
        if not args.unordered:
            for a in range(available):
                for b in range(a): cnf.add([-gate['select'][0][a],-gate['select'][1][b]])
                cnf.add([-gate['select'][0][a],-gate['select'][1][a],-gate['sign'][0],gate['sign'][1]])
    output_sign = cnf.fresh()
    cnf.add([-output_sign,marks[-1]])
    if args.used:
        for j in range(m-1): cnf.add([gates[t]['select'][s][N+1+j] for t in range(j+1,m) for s in range(2)])
    if args.lex:
        for j in range(m-1):
            left,right=gates[j],gates[j+1]
            available=N+1+j
            dependent=[right['select'][0][available],right['select'][1][available]]
            for a in range(available):
                for b in range(a):
                    cnf.add(dependent+[-left['select'][0][a],-right['select'][0][b]])
                for b in range(available):
                    for c in range(b):
                        cnf.add(dependent+[-left['select'][0][a],-right['select'][0][a],-left['select'][1][b],-right['select'][1][c]])
    row_values = {}
    for row in rows:
        values = [cnf.fresh() for _ in range(m)]
        row_values[row] = values
        for j,gate in enumerate(gates):
            effective = []
            for slot in range(2):
                raw, adjusted = cnf.fresh(),cnf.fresh()
                effective.append(adjusted)
                for source,selected in enumerate(gate['select'][slot]):
                    if source <= N:
                        val = source < N and bool((row >> source) & 1)
                        cnf.add([-selected,raw if val else -raw])
                    else:
                        old = values[source-N-1]
                        cnf.add([-selected,-raw,old]); cnf.add([-selected,raw,-old])
                cnf.xor(adjusted,raw,gate['sign'][slot])
            a,b = effective
            out,op = values[j],gate['or']
            for clause in ([op,-out,a],[op,-out,b],[op,out,-a,-b],[-op,out,-a],[-op,out,-b],[-op,-out,a,b]): cnf.add(clause)
        if target(row):
            cnf.add([values[-1],output_sign]); cnf.add([-values[-1],-output_sign])
        else:
            cnf.add([-values[-1],output_sign]); cnf.add([values[-1],-output_sign])
    if args.essential_mask is not None:
        for row,desired in [(3,False),(args.essential_mask,True),(0,False),(1023,True)]:
            for source,marked in enumerate(marks):
                if source <= N:
                    actual = source < N and bool((row >> source) & 1)
                    if actual != desired: cnf.add([-marked])
                else:
                    value = row_values[row][source-N-1]
                    cnf.add([-marked,value if desired else -value])
    cnf.finish()
    meta = {'n':N,'binary_gates':m,'not_count':None if args.unrestricted_negation else k,'unrestricted_negation':args.unrestricted_negation,'rows':rows,'row_values':row_values,'marks':marks,'gates':gates,'output_sign':output_sign,'vars':cnf.variables,'clauses':cnf.clauses,'ordered':not args.unordered,'all_gates_used':args.used,'lex':args.lex,'essential_mask':args.essential_mask,
            'normal_form':'AND/OR binary gates only; shared signed source wires; false input at10; binary outputs11+j; last binary gate output up to sign; repeated operands allowed. Witness search, not certified exhaustive lower bound.'}
    path.with_suffix('.meta.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps({'cnf':str(path),'meta':str(path.with_suffix('.meta.json')),'rows':len(rows),'vars':cnf.variables,'clauses':cnf.clauses}))

def decode(args):
    meta = json.loads(Path(args.meta).read_text())
    text = Path(args.model).read_text()
    if 's SATISFIABLE' not in text: raise SystemExit('No SATISFIABLE model status')
    positive = {int(v) for line in text.splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)>0}
    marked = [wire for wire,var in enumerate(meta['marks']) if var in positive]
    if meta['not_count'] is not None: assert len(marked) == meta['not_count']
    signed = []
    for gate in meta['gates']:
        sources = [[i for i,var in enumerate(slot) if var in positive] for slot in gate['select']]
        assert all(len(s)==1 for s in sources)
        operands = [(sources[s][0],gate['sign'][s] in positive) for s in range(2)]
        assert all(not sign or wire in marked for wire,sign in operands)
        signed.append(('OR' if gate['or'] in positive else 'AND',operands))
    output_sign = meta['output_sign'] in positive
    assert not output_sign or N+len(signed) in marked
    used_negative_sources = {wire for _,operands in signed for wire,sign in operands if sign}
    if output_sign: used_negative_sources.add(N+len(signed))
    emitted_marks = sorted(used_negative_sources) if meta['not_count'] is None else marked
    sentinel = N+len(signed)+len(emitted_marks)+1
    raw_map = {wire:wire for wire in range(N)}
    raw_map[N] = sentinel
    neg_map,expanded = {},[]
    def emit(op,sources):
        expanded.append((op,list(sources)))
        return N+len(expanded)-1
    for wire in emitted_marks:
        if wire<=N: neg_map[wire]=emit('NOT',[raw_map[wire]])
    for j,(op,operands) in enumerate(signed):
        remapped=[neg_map[wire] if sign else raw_map[wire] for wire,sign in operands]
        wire=N+1+j
        raw_map[wire]=emit(op,remapped)
        if wire in emitted_marks: neg_map[wire]=emit('NOT',[raw_map[wire]])
    final_wire=N+len(signed)
    output=neg_map[final_wire] if output_sign else raw_map[final_wire]
    assert len(expanded)==len(signed)+len(emitted_marks)
    bad=[]
    for row in range(1<<N):
        values=[bool((row>>v)&1) for v in range(N)]
        signed_values=values+[False]
        for op,operands in signed:
            a,b=[signed_values[wire]^sign for wire,sign in operands]
            signed_values.append((a and b) if op=='AND' else (a or b))
        signed_result=signed_values[-1]^output_sign
        for op,operands in expanded:
            ins=[values[wire] if wire<len(values) else False for wire in operands]
            values.append(all(ins) if op=='AND' else any(ins) if op=='OR' else not ins[0])
        result=values[output] if output<len(values) else False
        assert result==signed_result
        if result!=target(row): bad.append(row)
    assert not set(bad).intersection(meta['rows']), 'Encoding/decoding error on constrained rows'
    report={'marked':marked,'used_negative_sources':sorted(used_negative_sources),'used_negative_source_count':len(used_negative_sources),'emitted_not_count':len(emitted_marks),'signed_gates':signed,'output_sign':output_sign,'expanded_gates':expanded,'output':output,'gate_count':len(expanded),'correct_all_1024':not bad,'counterexamples':bad}
    Path(args.out).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'report':args.out,'gates':len(expanded),'not_count':len(emitted_marks),'used_negative_source_count':len(used_negative_sources),'correct_all_1024':not bad,'mismatch_count':len(bad),'first_mismatches':bad[:20]}))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    sub=p.add_subparsers(dest='command',required=True)
    gen=sub.add_parser('generate')
    gen.add_argument('--gates',type=int,default=18); gen.add_argument('--not-count',type=int,default=1)
    gen.add_argument('--rows',choices=['all','critical'],default='critical'); gen.add_argument('--extra-rows',default='')
    gen.add_argument('--essential-mask',type=int,default=None)
    gen.add_argument('--unrestricted-negation',action='store_true')
    gen.add_argument('--lex',action='store_true')
    gen.add_argument('--unordered',action='store_true'); gen.add_argument('--used',action='store_true'); gen.add_argument('--out',required=True)
    dec=sub.add_parser('decode')
    dec.add_argument('--meta',required=True); dec.add_argument('--model',required=True); dec.add_argument('--out',required=True)
    args=p.parse_args()
    generate(args) if args.command=='generate' else decode(args)

if __name__=='__main__': main()
