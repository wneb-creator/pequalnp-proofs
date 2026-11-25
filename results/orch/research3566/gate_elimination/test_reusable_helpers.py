import importlib.util,json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-178/gap3566/gate_elimination')
spec=importlib.util.spec_from_file_location('helpers',base/'reusable_helpers.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
p=Path('/tmp/oec/pequalnp-pilot-178/gap3566/finite_search/c8-12-with-helper.witness.json');r=json.loads(p.read_text())
a=h.audit_case(r['n'],r['edges'],r['gates']);assert len(a['helpers'])==1 and a['helpers'][0]['single_profit']==0
x=h.construct_extension(r['n'],r['edges'],r['gates'],r['n']+len(r['gates'])-1,a['helpers'])
info,tau,F=h.graph_data(x['n'],tuple(sorted(tuple(sorted(e)) for e in x['edges'])))
v,_,_,_=h.normalize(x['n'],x['gates'],x['output']);assert v[x['output']]==F
assert len(x['gates'])==15 and len(x['edges'])+tau-1==15
x['inputs']=x['n'];x['left']=[i for i,c in enumerate(info[1]) if c==0];x['right']=[i for i,c in enumerate(info[1]) if c==1]
x['edges']=[(u,v) if info[1][u]==0 else (v,u) for u,v in x['edges']]
(base/'helper-extension-positive-control.json').write_text(json.dumps({'witness':x},indent=2)+'\n')
old=[(0,1),(2,3)];helpers=[{'support':[0,2]},{'support':[0,3]}]
assert h.color_graph(6,h.extended_edges(4,old,helpers[:1])) is not None
assert h.color_graph(6,h.extended_edges(4,old,helpers[1:])) is not None
assert h.color_graph(8,h.extended_edges(4,old,helpers)) is None
print('PASS: 15-gate C8 extension has exact full truth function and bound; incompatible component flips rejected jointly.')
