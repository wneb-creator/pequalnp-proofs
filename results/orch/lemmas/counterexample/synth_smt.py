#!/usr/bin/env python3
import argparse
from pathlib import Path
p=argparse.ArgumentParser(); p.add_argument('--N',type=int,required=True); p.add_argument('--edges',required=True); p.add_argument('--size',type=int,required=True); p.add_argument('--clean',action='store_true'); p.add_argument('--lex',action='store_true'); p.add_argument('--boundary',action='store_true'); p.add_argument('--out',required=True); p.add_argument('--timeout-ms',type=int,default=60000); a=p.parse_args()
N=a.N; n=2*N; s=a.size; rows=1<<n
edges=[tuple(map(int,e.split(':'))) for e in a.edges.split(',')]
assert edges and all(0<=i<N and 0<=j<N for i,j in edges)
assert not any(all((i,j) in edges for i in [p,q] for j in [l,m]) for p in range(N) for q in range(p+1,N) for l in range(N) for m in range(l+1,N))
target=lambda r:any((r>>i&1) and (r>>(N+j)&1) for i,j in edges)
forbidden={1<<i for i in range(n)}|{(1<<i)|(1<<(N+j)) for i in range(N) for j in range(N) if (i,j) not in edges}
assignments=list(range(rows))
if a.boundary:
 assignments=sorted(forbidden|{(1<<i)|(1<<(N+j)) for i,j in edges}|{r for r in range(rows) if not target(r) and all(target(r|(1<<i)) for i in range(n) if not r>>i&1)})
 rows=len(assignments)
truebits=sum(1<<k for k,r in enumerate(assignments) if target(r))
inputbits=[sum(1<<k for k,r in enumerate(assignments) if r>>i&1) for i in range(n)]
fbd=sum(1<<k for k,r in enumerate(assignments) if r in forbidden)
idxbits=(n+s-1).bit_length()
def b(v,width=rows): return f'(_ bv{v} {width})'
def decl(name,sort): return f'(declare-fun {name} () {sort})'
lines=['(set-logic QF_BV)',f'(set-option :timeout {a.timeout_ms})','(set-option :produce-models true)']
for j in range(s):
 lines += [decl(f'a{j}',f'(_ BitVec {idxbits})'),decl(f'b{j}',f'(_ BitVec {idxbits})'),decl(f'and{j}','Bool'),decl(f'w{j}',f'(_ BitVec {rows})')]
 lines += [f'(assert (bvult a{j} b{j}))',f'(assert (bvult b{j} {b(n+j,idxbits)}))']
 def mux(side):
  terms=[b(v) for v in inputbits]+[f'w{i}' for i in range(j)]
  t=terms[-1]
  for k in reversed(range(len(terms)-1)): t=f'(ite (= {side}{j} {b(k,idxbits)}) {terms[k]} {t})'
  return t
 lines += [f'(define-fun x{j} () (_ BitVec {rows}) {mux("a")})',f'(define-fun y{j} () (_ BitVec {rows}) {mux("b")})',f'(assert (= w{j} (ite and{j} (bvand x{j} y{j}) (bvor x{j} y{j}))))']
 if a.clean: lines += [f'(assert (=> and{j} (= (bvand w{j} {b(fbd)}) {b(0)})))']
if a.lex:
 for j in range(s-1):
  independent=f'(and (distinct a{j+1} {b(n+j,idxbits)}) (distinct b{j+1} {b(n+j,idxbits)}))'
  lex=f'(or (bvult a{j} a{j+1}) (and (= a{j} a{j+1}) (or (bvult b{j} b{j+1}) (and (= b{j} b{j+1}) (or and{j} (not and{j+1}))))))'
  lines += [f'(assert (=> {independent} {lex}))']
# Every gate contributes to output in a genuinely least-size circuit. We search each size.
for j in range(s-1):
 use=[f'(= {side}{k} {b(n+j,idxbits)})' for k in range(j+1,s) for side in ['a','b']]
 lines += ['(assert (or '+' '.join(use)+'))']
# In a least circuit no two gates compute equal tables and no gate duplicates an input.
for j in range(s):
 for i in range(j): lines += [f'(assert (distinct w{j} w{i}))']
 for v in inputbits: lines += [f'(assert (distinct w{j} {b(v)}))']
lines += [f'(assert (= w{s-1} {b(truebits)}))','(check-sat)','(get-model)']
Path(a.out).write_text('\n'.join(lines)+'\n')
print(f'N={N} size={s} clean={a.clean} edges={edges} rows={rows} bytes={Path(a.out).stat().st_size}')
