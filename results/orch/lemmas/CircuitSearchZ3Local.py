import sys,time,json,ctypes,re
from pathlib import Path
p=int(sys.argv[1]);l=int(sys.argv[2]);k=int(sys.argv[3]);graph=sys.argv[4];timeout=int(sys.argv[5]);dirty=len(sys.argv)>6 and sys.argv[6]=='dirty';n=p+l
if graph=='cycle6': E={(0,3),(0,4),(1,4),(1,5),(2,5),(2,3)}
elif graph=='cycle8': E={(i,4+i) for i in range(4)}|{(i,4+(i+1)%4) for i in range(4)}
elif graph=='fano': E={(a,7+b) for a in range(7) for b in range(7) if (a-b)%7 in (0,1,3)}
elif graph=='fano55': E={(a,5+b) for a,b in ((0,0),(0,4),(1,0),(1,1),(2,1),(2,2),(3,0),(3,2),(3,3),(4,1),(4,3),(4,4))}
elif graph=='theta10': E={(0,5+b) for b in range(1,5)}|{(a,5+b) for a in range(1,5) for b in (0,a)}
elif graph=='theta8': E={(0,4),(0,5),(0,6),(1,4),(1,7),(2,5),(2,7),(3,6),(3,7)}
else:E={tuple(map(int,e.split(','))) for e in graph.split(';')}
assert p >= 0 and l >= 0 and k > 0
assert all(0 <= a < p and p <= b < n for a,b in E), 'edges outside fixed bipartition'
assert all(not all((a,b) in E for a in (a0,a1) for b in (b0,b1))
           for a0 in range(p) for a1 in range(a0+1,p)
           for b0 in range(p,n) for b1 in range(b0+1,n)), 'graph has a four-cycle'
def target(x):return any(x>>a&1 and x>>b&1 for a,b in E)
positive=sorted((1<<a)|(1<<b) for a,b in E)
negative=[x for x in range(1<<n) if not target(x) and all(target(x|(1<<v)) for v in range(n) if not (x>>v&1))]
inputs=positive+negative;m=len(inputs);w=(n+k).bit_length()
def bv(x,width):return f'(_ bv{x} {width})'
def select(names,v):
 out=names[-1]
 for i in reversed(range(len(names)-1)):out=f'(ite (= {v} {bv(i,w)}) {names[i]} {out})'
 return out
vals=[bv(sum((x>>v&1)<<d for d,x in enumerate(inputs)),m) for v in range(n)]
colors=[bv(1 if v<p else 2,2) for v in range(n)]
lines=[f'(set-option :timeout {timeout*1000})','(set-option :memory_max_size 2048)','(set-logic QF_BV)']
for g in range(k):
 lines += [f'(declare-fun a{g} () (_ BitVec {w}))',f'(declare-fun b{g} () (_ BitVec {w}))',f'(declare-fun o{g} () Bool)',f'(assert (bvule a{g} b{g}))',f'(assert (bvult b{g} {bv(n+g,w)}))']
 for side in 'ab':
  lines += [f'(define-fun {side}v{g} () (_ BitVec {m}) {select(vals,side+str(g))})',f'(define-fun {side}c{g} () (_ BitVec 2) {select(colors,side+str(g))})']
 lines += [f'(define-fun v{g} () (_ BitVec {m}) (ite o{g} (bvand av{g} bv{g}) (bvor av{g} bv{g})))',f'(define-fun c{g} () (_ BitVec 2) (ite o{g} {bv(0,2)} (bvor ac{g} bc{g})))',f'(assert (not (= c{g} {bv(3,2)})))']
 vals.append('v'+str(g));colors.append('c'+str(g))
for g in range(k):
 lines.append(f'(assert (or o{g} (not (= a{g} b{g}))))')
 for h in range(g):
  lines.append(f'(assert (not (and (= a{g} a{h}) (= b{g} b{h}) (= o{g} o{h}))))')
for g in range(k-1):
 key0=f'(concat a{g} (concat b{g} (ite o{g} #b0 #b1)))'
 key1=f'(concat a{g+1} (concat b{g+1} (ite o{g+1} #b0 #b1)))'
 lines.append(f'(assert (or (= a{g+1} {bv(n+g,w)}) (= b{g+1} {bv(n+g,w)}) (bvule {key0} {key1})))')
if graph in ('cycle6','fano'):
 # Search symmetry restriction: graph automorphisms normalize first operand pairs.
 edge=3 if graph=='cycle6' else 7
 nonedge=5 if graph=='cycle6' else 8
 lines.append(f'(assert (= a0 {bv(0,w)}))')
 andopts=' '.join(f'(= b0 {bv(b,w)})' for b in (0,1,edge,nonedge))
 lines.append(f'(assert (ite o0 (or {andopts}) (= b0 {bv(1,w)})))')
for v in sorted({v for edge in E for v in edge}):
 terms=[f'(= {side}{g} {bv(v,w)})' for g in range(k) for side in 'ab']
 lines.append('(assert (or '+' '.join(terms)+'))')
for g in range(k-1):
 terms=[f'(= {side}{h} {bv(n+g,w)})' for h in range(g+1,k) for side in 'ab']
 lines.append('(assert (or '+' '.join(terms)+'))')
lines.append(f'(assert (= v{k-1} {bv((1<<len(positive))-1,m)}))')
if dirty:
 mask=((1<<m)-1)^((1<<len(positive))-1)
 positive_mask=(1<<len(positive))-1
 terms=[]
 for g in range(k):
  accepted=f'(bvand v{g} {bv(positive_mask,m)})'
  at_least_two=f'(not (= (bvand {accepted} (bvsub {accepted} {bv(1,m)})) {bv(0,m)}))'
  terms.append(f'(and o{g} (not (= (bvand v{g} {bv(mask,m)}) {bv(0,m)})) {at_least_two})')
 lines.append('(assert (or '+' '.join(terms)+'))')
smt='\n'.join(lines)+'\n'
print(json.dumps({'n':n,'k':k,'E':sorted(E),'samples':len(inputs),'dirty':dirty,'multi_dirty':dirty,'backend':'qfbv-sls','smt_bytes':len(smt)}),flush=True)
z=ctypes.CDLL('/usr/lib/x86_64-linux-gnu/libz3.so.4')
z.Z3_mk_config.restype=ctypes.c_void_p;z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_del_config.argtypes=[ctypes.c_void_p];z.Z3_del_context.argtypes=[ctypes.c_void_p]
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
def ev(s):return z.Z3_eval_smtlib2_string(ctx,s.encode()).decode()
start=time.time();result=ev(smt+'(check-sat-using qfbv-sls)\n');print('result',result.strip(),'elapsed',time.time()-start,flush=True)
if result.strip()=='sat':
 names=[f'{v}{g}' for g in range(k) for v in 'abo'];model=ev('(get-value ('+' '.join(names)+'))');print(model,flush=True)
 pairs=re.findall(r'\(([abo]\d+)\s+(true|false|#x[0-9a-f]+|#b[01]+|\(_ bv\d+ \d+\))\)',model)
 def value(s):
  if s in ('true','false'):return s=='true'
  if s.startswith('#x'):return int(s[2:],16)
  if s.startswith('#b'):return int(s[2:],2)
  return int(s.split()[1][2:])
 d={name:value(val) for name,val in pairs};gates=[(d['a'+str(g)],d['b'+str(g)],0 if d['o'+str(g)] else 1) for g in range(k)];print('gates',gates,flush=True)
 for g,(a,b,op) in enumerate(gates): assert 0 <= a <= b < n+g and op in (0,1), 'invalid gate'
 dirty_witnesses={}
 edge_accepts=[0]*k
 positive_set=set(positive)
 for x in range(1<<n):
  vs=[x>>v&1 for v in range(n)]
  for a,b,op in gates:vs.append(vs[a]|vs[b] if op else vs[a]&vs[b])
  assert bool(vs[-1])==target(x),(x,vs[-1])
  if x in positive_set:
   for g in range(k): edge_accepts[g]+=int(vs[n+g])
  if not target(x):
   for g,(a,b,op) in enumerate(gates):
    if op==0 and vs[n+g]: dirty_witnesses.setdefault(g,x)
 if dirty: assert any(edge_accepts[g]>=2 for g in dirty_witnesses), 'requested multi-edge dirty AND absent'
 print('multi_edge_dirty_gates',[g for g in dirty_witnesses if edge_accepts[g]>=2],flush=True)
 print('dirty_AND_witnesses',dirty_witnesses,flush=True)
 reach=[1 if v<p else 2 for v in range(n)]
 for a,b,op in gates:
  r=reach[a]|reach[b] if op else 0;assert r!=3;reach.append(r)
 print('FULL TRUTH TABLE AND COLOR VALIDATED',flush=True)
else:print(ev('(get-info :reason-unknown)'),flush=True)
z.Z3_del_context(ctx)
