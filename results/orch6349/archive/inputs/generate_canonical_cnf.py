#!/usr/bin/env python3
"""Exact ordered translation of LRAT.Link.enc2 8 9 on Promise.rows44."""
import hashlib
import json
from pathlib import Path

ROOT = Path('/tmp/oec/pequalnp-pilot-61')
n, s = 8, 9
wd = 2**n + n + s + 1
rows = [2**u + 2**(4+v) for u in range(4) for v in range(4)]
truth = {2**u + 2**(4+v): bool((5805 >> (4*u+v)) & 1)
         for u in range(4) for v in range(4)}
def ix(kd, j, a): return (kd*(s+1)+j)*wd+a
def p(kd,j,a): return ix(kd,j,a)+1
def q(kd,j,a): return -p(kd,j,a)
def lit(kd,j,a,b): return p(kd,j,a) if b else q(kd,j,a)
families = {}
families['fOp'] = [[p(0,j,0),p(0,j,1),p(0,j,2)] for j in range(s)]
families['fSrcAlo'] = [[p(e,j,k) for k in range(n+j+1)]
                      for e in (1,2) for j in range(s)]
def src_eq(e,j,k,r):
    if k<n: return [[q(e,j,k),lit(e+3,j,r,bool((r>>k)&1))]]
    if k<n+j: return [[q(e,j,k),q(e+3,j,r),p(3,k-n,r)],
                      [q(e,j,k),p(e+3,j,r),q(3,k-n,r)]]
    return [[q(e,j,k),q(e+3,j,r)]]
families['fSrcEq'] = [c for e in (1,2) for j in range(s) for r in rows
                      for k in range(n+j+1) for c in src_eq(e,j,k,r)]
def gate_cl(j,r):
    return [[q(0,j,0),q(3,j,r),p(4,j,r)],
            [q(0,j,0),q(3,j,r),p(5,j,r)],
            [q(0,j,0),p(3,j,r),q(4,j,r),q(5,j,r)],
            [q(0,j,1),p(3,j,r),q(4,j,r)],
            [q(0,j,1),p(3,j,r),q(5,j,r)],
            [q(0,j,1),q(3,j,r),p(4,j,r),p(5,j,r)],
            [q(0,j,2),p(3,j,r)]]
families['fGate'] = [c for j in range(s) for r in rows for c in gate_cl(j,r)]
families['fOutAlo'] = [[p(6,0,k) for k in range(n+s+1)]]
def out_eq(k,r):
    if k<n: return [] if bool((r>>k)&1)==truth[r] else [[q(6,0,k)]]
    if k<n+s: return [[q(6,0,k),lit(3,k-n,r,truth[r])]]
    return [[q(6,0,k)]] if truth[r] else []
families['fOutEq'] = [c for r in rows for k in range(n+s+1) for c in out_eq(k,r)]
families['fOut'] = [[p(6,0,n+s-1),p(7,s-1,0)]]
families['fPad'] = [c for j in range(s) for c in [
    [q(7,j,0),p(0,j,2)], [q(7,j,0),p(1,j,n+j)], [q(7,j,0),p(2,j,n+j)],
    [p(7,j,0),q(0,j,2)], [p(7,j,0),q(1,j,n+j)], [p(7,j,0),q(2,j,n+j)]]]
families['fPre'] = [[q(7,j+1,0),p(7,j,0)] for j in range(s-1)]
families['fPadRd'] = [c for j in range(s) for i in range(j) for c in
                    [[q(7,i,0),q(1,j,n+i)],[q(7,i,0),q(2,j,n+i)]]]
families['fOrd'] = [[q(1,j,k),q(2,j,l),p(7,j,0)]
                    for j in range(s) for k in range(n+j+1) for l in range(k+1)]
families['fUsed'] = [[p(1,j+1+t,n+j) for t in range(s-1-j)] +
                     [p(2,j+1+t,n+j) for t in range(s-1-j)] + [p(7,j,0)]
                     for j in range(s-1)]
def lex_base(j): return [p(7,j,0),p(1,j+1,n+j),p(2,j+1,n+j)]
lex=[]
for j in range(s-1):
    for a in range(n+j+1):
        lex += [[q(1,j,a),q(1,j+1,b)]+lex_base(j) for b in range(a)]
        for c in range(n+j+1):
            lex += [[q(1,j,a),q(1,j+1,a),q(2,j,c),q(2,j+1,d)]+lex_base(j)
                    for d in range(c)]
            lex += [[q(1,j,a),q(1,j+1,a),q(2,j,c),q(2,j+1,c),q(0,j,1)]+lex_base(j),
                    [q(1,j,a),q(1,j+1,a),q(2,j,c),q(2,j+1,c),q(0,j+1,0)]+lex_base(j)]
families['fLex']=lex
clauses = [c for cs in families.values() for c in cs]
max_var=max(abs(l) for c in clauses for l in c)
body=f'p cnf {max_var} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
path=ROOT/'canonical6349.cnf'
path.write_text(body)
manifest={'n':n,'s':s,'width':wd,'rows':rows,'truth':[truth[r] for r in rows],
          'families':{k:len(v) for k,v in families.items()},'variables':max_var,
          'clauses':len(clauses),'bytes':len(body),'sha256':hashlib.sha256(body.encode()).hexdigest()}
(ROOT/'canonical6349-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest,indent=2))
