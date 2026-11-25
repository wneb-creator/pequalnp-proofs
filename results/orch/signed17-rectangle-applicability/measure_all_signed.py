from pathlib import Path
import ctypes,json,time,sys,random,collections,hashlib
p=Path(__file__).resolve().parent;sys.path.insert(0,str(p.parent));import test_all_rectangles as old
src=p.parent.parent/'library_route/signed17-joint-measurement/leaf-banks.json';d=json.loads(src.read_text());certs=old.CERTS+json.loads((p.parent/'dynamic-loader/matrices-v5.json').read_text())
lib=ctypes.CDLL(str(p/'rectangle_dynamic.so'));lib.rectangle_dynamic.argtypes=[ctypes.c_int,ctypes.c_int,ctypes.POINTER(ctypes.c_longlong),ctypes.c_uint,ctypes.c_uint];lib.rectangle_dynamic.restype=ctypes.c_longlong
arrays=[(ctypes.c_longlong*(len(c['weights'])*len(c['weights'][0])))(*(x for row in c['weights'] for x in row)) for c in certs];cache=[{} for _ in certs]
def rectangle(c,pm,nm):
 key=pm,nm
 if key not in cache[c]:cache[c][key]=int(lib.rectangle_dynamic(len(certs[c]['weights']),len(certs[c]['weights'][0]),arrays[c],pm,nm))
 return cache[c][key]
rng=random.Random(2373)
for i,c in enumerate(old.CERTS):
 for _ in range(30):
  pm=rng.randrange(1<<len(c['positive_rows']));nm=rng.randrange(1<<len(c['negative_rows']));assert rectangle(i,pm,nm)==old.LIB.rectangle_cost(i,pm,nm)
start=time.monotonic();signals=[int(x,16) for x in d['signals']];pos=[];both=[]
for g in signals:
 ps=[];bs=[]
 for i,c in enumerate(certs):
  pm=sum(((g>>r)&1)<<j for j,r in enumerate(c['positive_rows']));nm=sum((1-((g>>r)&1))<<j for j,r in enumerate(c['negative_rows']));a=rectangle(i,pm,nm);b=rectangle(i,pm^((1<<len(c['positive_rows']))-1),nm^((1<<len(c['negative_rows']))-1));ps.append(a);bs.append(max(a,b))
 pos.append(ps);both.append(bs)
rows=[]
for bank in d['banks']:
 pc=[sum(pos[s][i] for s in bank['state']) for i in range(len(certs))];bc=[sum(both[s][i] for s in bank['state']) for i in range(len(certs))];rows.append(dict(part=bank['part'],node=bank['node'],kind=bank['kind'],roots=bank['roots'],positive_margins=[c['total']-v for c,v in zip(certs,pc)],both_margins=[c['total']-v for c,v in zip(certs,bc)]))
summary={}
for group in ['edge','nonedge','union']:
 for kind in ['formula0','formula1']:
  rs=[x for x in rows if x['kind']==kind and (group=='union' or group in x['roots'])];best=max(((v/certs[i]['total'],x['part'],x['node'],i,v) for x in rs for i,v in enumerate(x['both_margins'])))
  summary[group+'_'+kind]=dict(banks=len(rs),positive_only_margins=sum(max(x['positive_margins'])>0 for x in rs),both_polarity_margins=sum(max(x['both_margins'])>0 for x in rs),best_normalized_margin=best)
result=dict(source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),matrices=len(certs),banks=len(rows),signals=len(signals),seconds=time.monotonic()-start,unique_profiles=sum(len(x) for x in cache),selftest='390 exact comparisons against prior fixed-matrix implementation PASS',summary=summary,scope='Exact integer research measurement, no new Lean or signed rectangle theorem. Formula1 parent diagnostic does not discharge sharing children.')
(p/'all-signed-summary.json').write_text(json.dumps(result,indent=2));(p/'all-signed-bank-margins.json').write_text(json.dumps(rows,indent=2));(p/'all-signed-matrices.json').write_text(json.dumps(certs,indent=2));print(json.dumps(result,indent=2))
