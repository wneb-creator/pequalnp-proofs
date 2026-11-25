import importlib.util,json,time
from pathlib import Path
path=Path('/tmp/oec/pequalnp-pilot-87/counterexample/one-not-local/focused.py')
spec=importlib.util.spec_from_file_location('focused_check',path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
gs=json.loads(path.with_name('trial-000.json').read_text())['seed']
def check(name,gs,exact,expected):
 c=m.Encode(gs,set(range(len(gs))),None,exact)
 for i,(op,a,b)in enumerate(gs):
  for v in [c.typ[i][op],c.left[i][a],c.right[i][b]]:c.clause(v)
 for row in range(1024):c.row(row)
 sl=m.solver();c.load(sl);m.end=time.monotonic()+30
 tick=time.monotonic();result=m.lib.sat_solve(sl);m.lib.sat_release(sl)
 print(json.dumps({'control':name,'result':result,'expected':expected,'variables':c.n,'clauses':len(c.cs),'seconds':time.monotonic()-tick}),flush=True)
 assert result==expected
check('all20dynamic_pins_fixed_known_positive',gs,False,10)
check('same20fixed_but_exact_one_NOT_contradiction',gs,True,20)
m.target=lambda row:not bool(row&1)
check('dynamic_NOT_x0_followed_by_OR_false',[(2,1,0),(1,0,11)],True,10)
print('ALL_CONTROLS_PASS',flush=True)
