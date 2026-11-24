import ctypes, sys, re, json, time
from pathlib import Path
vals=[256463372304,8521482511360,14003410187716736,55389823206179104,155696362464215096,218994303131713984,183565875465424384,229736628136996864,270286071508729856,288160007409369088,192860064594267704,288166778660192704,283797140973809664]
target=1764784
n=int(sys.argv[1]) if len(sys.argv)>1 else 14
ms=int(sys.argv[2]) if len(sys.argv)>2 else 120000
seed=int(sys.argv[3]) if len(sys.argv)>3 else 0
out=Path('/tmp/oec/pequalnp-pilot-42/sat')
width=max(vals).bit_length()
s=[f'(set-option :timeout {ms})',f'(set-option :sat.random_seed {seed})','(set-option :produce-models true)','(set-logic QF_BV)']
for k,v in enumerate(vals):s.append(f'(define-fun v{k} () (_ BitVec {width}) (_ bv{v} {width}))')
for k in range(13,13+n):
 s += [f'(declare-fun a{k} () (_ BitVec 5))',f'(declare-fun b{k} () (_ BitVec 5))',f'(declare-fun o{k} () Bool)',f'(declare-fun v{k} () (_ BitVec {width}))',f'(assert (bvult a{k} b{k}))',f'(assert (bvult b{k} (_ bv{k} 5)))']
 for arg in ['a','b']:
  expr=f'v{k-1}'
  for j in range(k-2,-1,-1):expr=f'(ite (= {arg}{k} (_ bv{j} 5)) v{j} {expr})'
  s.append(f'(define-fun {arg}v{k} () (_ BitVec {width}) {expr})')
 s += [f'(assert (= v{k} (ite o{k} (bvor av{k} bv{k}) (bvand av{k} bv{k}))))']
 # avoid duplicate prior gates, implied by size-minimality
 for j in range(13,k):s.append(f'(assert (not (= v{k} v{j})))')
s.append(f'(assert (= v{12+n} (_ bv{target} {width})))')
for k in range(13,12+n):
 refs=[]
 for j in range(k+1,13+n):refs += [f'(= a{j} (_ bv{k} 5))',f'(= b{j} (_ bv{k} 5))']
 s.append('(assert (or '+' '.join(refs)+'))')
s += ['(check-sat)','(get-model)']
txt='\n'.join(s)
(out/f'query-{n}-{seed}.smt2').write_text(txt)
z=ctypes.CDLL('libz3.so.4')
z.Z3_mk_config.restype=ctypes.c_void_p
z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p
z.Z3_del_config.argtypes=[ctypes.c_void_p]
z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
print('start',time.time(),'gates',n,'width',width,flush=True)
res=z.Z3_eval_smtlib2_string(ctx,txt.encode()).decode()
(out/f'model-{n}-{seed}.txt').write_text(res)
print(res,flush=True)
