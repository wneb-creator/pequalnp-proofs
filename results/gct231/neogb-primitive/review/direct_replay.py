"""Direct polynomial-state replay, independent of the author's vector/DAG replay."""
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
import json, re, hashlib
from verify_certificate import input_polynomials

base=Path(__file__).resolve().parent.parent
tracebase=base/'sparse-engine/certificate-trace-primitive'

def check(stem):
    names,generators=input_polynomials(tracebase/(stem+'.f4.in'))
    n=len(names);position={name:i for i,name in enumerate(names)}
    def parse(text):
        if not text:return {}
        pieces=re.findall(r'\(([^()]*)\)',text)
        assert ' + '.join('('+piece+')' for piece in pieces)==text
        result={}
        for piece in pieces:
            factors=piece.split('*');coeff=Q(factors.pop(0));exponents=[0]*n
            for factor in factors:
                if factor=='1':continue
                variable,power=factor.split('^')
                assert variable in position
                degree=int(power);assert degree>=0
                exponents[position[variable]]+=degree
            key=tuple(exponents)
            result[key]=result.get(key,Q(0))+coeff
        return {key:value for key,value in result.items() if value}
    def add(left,right,scale):
        result=left.copy()
        for key,value in right.items():result[key]=result.get(key,Q(0))+scale*value
        return {key:value for key,value in result.items() if value}
    def derive_input(row,known):
        # Search exact shifted scalar equality, with no normalized shape table.
        assert row
        low=tuple(min(key[j] for key in row) for j in range(n))
        for old in known:
            if len(old)!=len(row):continue
            oldlow=tuple(min(key[j] for key in old) for j in range(n))
            shift=tuple(low[j]-oldlow[j] for j in range(n))
            if min(shift)<0:continue
            first=next(iter(old));translated=tuple(first[j]+shift[j] for j in range(n))
            if translated not in row:continue
            factor=row[translated]/old[first]
            expected={tuple(key[j]+shift[j] for j in range(n)):value*factor for key,value in old.items()}
            if expected==row:return
        raise AssertionError('Input row is not a monomial multiple of an established polynomial')
    states={};known=[];counts=Counter();lastid=0;constants=[];published=set()
    trace=tracebase/(stem+'.trace')
    for line in trace.read_text().splitlines():
        fields=line.split('\t');op=fields[0];counts[op]+=1
        if op=='G':
            assert len(fields)==3
            idx=int(fields[1]);assert 0<=idx<len(generators)
            row=parse(fields[2]);assert row==generators[idx];known.append(row)
        elif op in ('I','M','S','A'):
            idx=int(fields[1]);assert idx>lastid and idx not in states;lastid=idx
            if op=='I':
                assert len(fields)==3
                row=parse(fields[2]);derive_input(row,known)
            elif op=='M':
                assert len(fields)==4
                parent=int(fields[2]);assert parent in published and parent in states
                shift=tuple(map(int,fields[3].split(',')))
                assert len(shift)==n and min(shift)>=0
                row={tuple(key[j]+shift[j] for j in range(n)):value for key,value in states[parent].items()}
            elif op=='S':
                assert len(fields)==4
                old=int(fields[2]);assert old in states
                scale=Q(fields[3]);row={key:value*scale for key,value in states[old].items() if value*scale}
            else:
                assert len(fields)==5
                left,right=map(int,fields[2:4]);assert left in states and right in states
                row=add(states[left],states[right],Q(fields[4]))
            states[idx]=row
        elif op=='O':
            assert len(fields)==3
            idx=int(fields[1]);actual=parse(fields[2])
            assert idx in states and actual==states[idx],('Wrong raw output',stem,idx)
            if actual:
                known.append(actual);published.add(idx)
                if set(actual)=={(0,)*n}:constants.append(str(actual[(0,)*n]))
        else:raise AssertionError(('Bad record',op))
    cert=json.loads((tracebase/(stem+'.certificate.json')).read_text())
    assert counts==cert['record_counts']
    assert bool(constants)==cert['proved_nonzero_constant']
    print(json.dumps(dict(stem=stem,trace_sha256=hashlib.sha256(trace.read_bytes()).hexdigest(),
        counts=counts,nonzero_constants=constants,verdict='PASS')),flush=True)

for stem in ('toy-unit','toy-nonunit','toy-rational','rowzero'):check(stem)

# Independent original -> sparse -> renamed companion identity check.
names,original=input_polynomials(base/'trace-rowzero.in')
renamed,companion=input_polynomials(tracebase/'rowzero.f4.in')
assert original==companion
tokens=list(map(int,(base/'sparse-engine/certificate-trace/rowzero.in').read_text().split()))
n,m,char,total=tokens[:4];assert (n,m,char,total)==(4,11,0,98)
lengths=tokens[4:4+m];assert sum(lengths)==total
offset=4+m;sparse=[]
for count in lengths:
    row={}
    for _ in range(count):
        numerator,denominator=tokens[offset:offset+2]
        exponent=tuple(tokens[offset+2:offset+2+n]);offset+=2+n
        assert len(exponent)==n and min(exponent)>=0 and exponent not in row
        row[exponent]=Q(numerator,denominator)
    sparse.append(row)
assert offset==len(tokens) and sparse==original
print('PASS exact original11equations/98terms -> sparse -> x0,x1,x2,x3 companion')
