import ctypes, json, re, sys, time

family=sys.argv[1]; k=int(sys.argv[2]); timeout=int(sys.argv[3])
if family=='fano':
 n=7; rows=[{b for b in range(7) if (a-b)%7 in (0,1,3)} for a in range(7)]
elif family=='fano55':
 n=5; rows=[{0,4},{0,1},{1,2},{0,2,3},{1,3,4}]
else: raise ValueError('unknown family')
assert k>0 and all(len(row)>=2 and all(0<=v<n for v in row) for row in rows)
assert all(len(rows[a]&rows[b])<=1 for a in range(n) for b in range(a+1,n))
assert all(i in rows[i] for i in range(n))
samples=sorted({1<<v for v in range(n)}|{((1<<n)-1)^sum(1<<v for v in row) for row in rows})
m=len(samples); w=(n+k).bit_length()
def bv(x,width):return f'(_ bv{x} {width})'
def select(names,var):
 out=names[-1]
 for i in reversed(range(len(names)-1)):out=f'(ite (= {var} {bv(i,w)}) {names[i]} {out})'
 return out
values=[bv(sum((x>>v&1)<<d for d,x in enumerate(samples)),m) for v in range(n)]
lines=[f'(set-option :timeout {timeout*1000})','(set-option :memory_max_size 2048)','(set-logic QF_BV)']
for g in range(k):
 lines.extend([f'(declare-fun a{g} () (_ BitVec {w}))',f'(declare-fun b{g} () (_ BitVec {w}))',f'(declare-fun o{g} () Bool)',f'(assert (bvule a{g} b{g}))',f'(assert (bvult b{g} {bv(n+g,w)}))'])
 for side in 'ab':lines.append(f'(define-fun {side}v{g} () (_ BitVec {m}) {select(values,side+str(g))})')
 lines.append(f'(define-fun v{g} () (_ BitVec {m}) (ite o{g} (bvand av{g} bv{g}) (bvor av{g} bv{g})))')
 values.append('v'+str(g))
 lines.append(f'(assert (or o{g} (not (= a{g} b{g}))))')
 for h in range(g):lines.append(f'(assert (not (and (= a{g} a{h}) (= b{g} b{h}) (= o{g} o{h}))))')
for a,row in enumerate(rows):
 lines.append(f'(declare-fun r{a} () (_ BitVec {w}))')
 lines.append(f'(assert (bvult r{a} {bv(n+k,w)}))')
 target=sum(int(any(x>>v&1 for v in row))<<d for d,x in enumerate(samples))
 lines.append(f'(assert (= {select(values,"r"+str(a))} {bv(target,m)}))')
 # A last AND computing a linear OR has one operand computing that same OR.
 alternatives=[f'(and (= r{a} {bv(n+g,w)}) (not o{g}))' for g in range(k)]
 lines.append('(assert (or '+' '.join(alternatives)+'))')
 for b in range(a):lines.append(f'(assert (not (= r{a} r{b})))')
for g in range(k):
 uses=[f'(= {side}{h} {bv(n+g,w)})' for h in range(g+1,k) for side in 'ab']+[f'(= r{a} {bv(n+g,w)})' for a in range(n)]
 lines.append('(assert (or '+' '.join(uses)+'))')
for v in range(n):
 uses=[f'(= {side}{g} {bv(v,w)})' for g in range(k) for side in 'ab']
 lines.append('(assert (or '+' '.join(uses)+'))')
for g in range(k-1):
 key0=f'(concat a{g} (concat b{g} (ite o{g} #b0 #b1)))';key1=f'(concat a{g+1} (concat b{g+1} (ite o{g+1} #b0 #b1)))'
 lines.append(f'(assert (or (= a{g+1} {bv(n+g,w)}) (= b{g+1} {bv(n+g,w)}) (bvule {key0} {key1})))')
smt='\n'.join(lines)+'\n'
print(json.dumps({'search':'OR-neighborhood multioutput synthesis','family':family,'n':n,'k':k,'rows':[sorted(row) for row in rows],'samples':samples,'smt_bytes':len(smt)}),flush=True)
z=ctypes.CDLL('/usr/lib/x86_64-linux-gnu/libz3.so.4')
z.Z3_mk_config.restype=ctypes.c_void_p;z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_del_config.argtypes=[ctypes.c_void_p];z.Z3_del_context.argtypes=[ctypes.c_void_p]
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
def ev(s):return z.Z3_eval_smtlib2_string(ctx,s.encode()).decode()
start=time.time();result=ev(smt+'(check-sat)\n');print('result',result.strip(),'elapsed',time.time()-start,flush=True)
if result.strip()=='sat':
 names=[f'{v}{g}' for g in range(k) for v in 'abo']+[f'r{a}' for a in range(n)]
 model=ev('(get-value ('+' '.join(names)+'))');print(model,flush=True)
 pairs=re.findall(r'\(([abor]\d+)\s+(true|false|#x[0-9a-f]+|#b[01]+|\(_ bv\d+ \d+\))\)',model)
 def value(s):
  if s in ('true','false'):return s=='true'
  if s.startswith('#x'):return int(s[2:],16)
  if s.startswith('#b'):return int(s[2:],2)
  return int(s.split()[1][2:])
 d={name:value(val) for name,val in pairs};gates=[(d['a'+str(g)],d['b'+str(g)],0 if d['o'+str(g)] else 1) for g in range(k)]
 outputs=[d['r'+str(a)] for a in range(n)]
 for g,(a,b,op) in enumerate(gates):assert 0<=a<=b<n+g and op in (0,1)
 assert all(0<=r<n+k for r in outputs)
 for x in range(1<<n):
  vs=[x>>v&1 for v in range(n)]
  for a,b,op in gates:vs.append(vs[a]|vs[b] if op else vs[a]&vs[b])
  for a,row in enumerate(rows):assert bool(vs[outputs[a]])==any(x>>v&1 for v in row),(x,a)
 print(json.dumps({'gates':gates,'outputs':outputs,'all_multioutput_assignments_validated':1<<n}),flush=True)
 full=[(a+n,b+n,op) for a,b,op in gates];stars=[]
 for a,r in enumerate(outputs):
  full.append((a,r+n,0));stars.append(2*n+len(full)-1)
 out=stars[0]
 for star in stars[1:]:
  full.append((out,star,1));out=2*n+len(full)-1
 reach=[1]*n+[2]*n
 for g,(a,b,op) in enumerate(full):
  assert 0<=a<2*n+g and 0<=b<2*n+g
  color=reach[a]|reach[b] if op else 0;assert color!=3;reach.append(color)
 for x in range(1<<(2*n)):
  vs=[x>>v&1 for v in range(2*n)]
  for a,b,op in full:vs.append(vs[a]|vs[b] if op else vs[a]&vs[b])
  assert bool(vs[out])==any(x>>a&1 and x>>(n+b)&1 for a,row in enumerate(rows) for b in row),x
 print(json.dumps({'full_circuit_gates':full,'full_circuit_output':out,'full_gate_count':len(full),'all_bipartite_assignments_and_colors_validated':1<<(2*n)}),flush=True)
else:print(ev('(get-info :reason-unknown)'),flush=True)
z.Z3_del_context(ctx)
