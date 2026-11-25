import argparse, ctypes, json, re, time
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--order',action='store_true');ap.add_argument('--input',required=True);ap.add_argument('--p',type=int,required=True);ap.add_argument('--l',type=int,required=True);ap.add_argument('--edges',required=True);ap.add_argument('--gates',type=int,required=True);ap.add_argument('--limit',type=int,default=600);ap.add_argument('--seed',type=int,default=71);ap.add_argument('--out',required=True);a=ap.parse_args()
E={tuple(map(int,e.split(','))) for e in a.edges.split(';')};n=a.p+a.l
text=Path(a.input).read_text();assert '(bvnot b0)' in text and '(bvnot a0)' in text
pairs=[(u,v) for u in range(n) for v in range(u+1,n) if not(u<a.p<=v and (u,v-a.p) in E)]
extra=[f'(assert (or (not {side}{j}s{u}) (not {side}{j}s{v})))' for j in range(a.gates) for side in ['a','b'] for u,v in pairs]
if a.order:
 extra += [f'(assert (or a{j}s{n+j-1} b{j}s{n+j-1} (bvule f{n+j-1} f{n+j})))' for j in range(1,a.gates)]
text=text.replace('(check-sat', '\n'.join(extra)+'\n(check-sat',1)
text=re.sub(r'\(set-option :timeout \d+\)',f'(set-option :timeout {a.limit*1000})',text)
text=re.sub(r'\(set-option :sat.random_seed \d+\)',f'(set-option :sat.random_seed {a.seed})',text)
Path(a.out+'.smt2').write_text(text)
z=ctypes.CDLL('libz3.so.4');z.Z3_mk_config.restype=ctypes.c_void_p;z.Z3_mk_context.argtypes=[ctypes.c_void_p];z.Z3_mk_context.restype=ctypes.c_void_p;z.Z3_del_config.argtypes=[ctypes.c_void_p];z.Z3_eval_smtlib2_string.argtypes=[ctypes.c_void_p,ctypes.c_char_p];z.Z3_eval_smtlib2_string.restype=ctypes.c_char_p;z.Z3_del_context.argtypes=[ctypes.c_void_p]
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg);t=time.monotonic();result=z.Z3_eval_smtlib2_string(ctx,text.encode()).decode();elapsed=time.monotonic()-t
if result.strip()=='sat':
 values=[f'{side}{j}s{i}' for j in range(a.gates) for side in ['a','b'] for i in range(n+j)]+[f'outs{i}' for i in range(n+a.gates)]
 result+=z.Z3_eval_smtlib2_string(ctx,('(get-value ('+' '.join(values)+'))').encode()).decode()
result+=f'Elapsed seconds: {elapsed}\nAdded redundant nonedge-pair clauses: {len(extra)}\n';Path(a.out+'.log').write_text(result);print(json.dumps(vars(a)),flush=True);print(result,flush=True);z.Z3_del_context(ctx)
