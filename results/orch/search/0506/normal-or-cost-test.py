from pathlib import Path
import ast,importlib.util,json,random,hashlib,time
B=Path('/tmp/oec/pequalnp-pilot-21/search')
spec=importlib.util.spec_from_file_location('normal_cost_runner',B/'cegis-normal-or-sinks-cost-stream.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
# Reuse only the independently reviewed propagation function, without executing old tests.
tree=ast.parse((B/'formal-cost-test.py').read_text());node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='propagate');namespace={};exec(compile(ast.Module(body=[node],type_ignores=[]),'reviewed_propagate','exec'),namespace);propagate=namespace['propagate']
c=m.f.b.CNF();ops=[c.var() for _ in range(38)];aa=[];bb=[]
for j in range(38):aa.append([c.var() for _ in range(13+j)]);bb.append([c.var() for _ in range(13+j)])
own=[c.var() for _ in range(13)];costs=m.normal_partition(c,ops,aa,bb,{'own_complement':own})
rng=random.Random(102413);accepted=rejected=0;started=time.monotonic()
for trial in range(64):
 assumptions=[];expected=[1]*13
 for j,op in enumerate(ops):
  a,b=sorted(rng.sample(range(13+j),2));is_and=(trial<16) if j<25 else False
  if 32<=trial and j<25:is_and=bool(rng.getrandbits(1))
  assumptions.append(op if is_and else -op)
  for sels,choice in ((aa[j],a),(bb[j],b)):assumptions.extend(v if k==choice else -v for k,v in enumerate(sels))
  expected.append(min(expected[a],expected[b]) if is_and else min(5,expected[a]+expected[b]))
 positive=trial>=48;assumptions.extend(v if positive and w==trial%13 else -v for w,v in enumerate(own))
 wanted=not positive and max(expected[-13:])==5
 model=propagate(c.cs,assumptions);assert (model is not None)==wanted
 if model is not None:
  accepted+=1
  for j,row in enumerate(costs):assert [model[v] for v in row]==[i==expected[13+j] for i in range(6)]
  assert all(any(model[abs(x)]==(x>0) for x in clause) for clause in c.cs)
 else:rejected+=1
class Count(m.f.b.CNF):
 def __init__(self):self.n=0;self.count=0
 def add(self,*xs):self.count+=1
m.f.CNF=Count
cc,oo,a,b=m.f.encode(list(m.f.INPUTS),[None]*13,list(range(13)),38,set(range(len(m.f.ROWS))),True)
cc.add(a[0][0]);cc.add(b[0][1]);cc.add(*oo)
for op in oo:cc.add(*(other for other in oo if other!=op))
for op in oo[25:]:cc.add(-op)
supports=m.h.reachability(cc,a,b,[None]*13,list(range(13)));m.h.live_sinks(cc,a,b,13,13);m.h.lex_internal(cc,oo,a,b,13)
boundary=m.h.offband_rows(cc,oo,a,b);exotic=m.h.nonordinary_lower_bound(cc,boundary,minimum=5);m.h.nonordinary_support(cc,exotic,supports[-13:]);m.normal_partition(cc,oo,a,b,boundary)
report={'status':'PASS','fixed_full38_networks':64,'accepted':accepted,'rejected':rejected,'full_variables':cc.n,'full_clauses':cc.count,'full_band_rows':3003,'solver_launched':False,'runner_sha256':hashlib.sha256((B/'cegis-normal-or-sinks-cost-stream.py').read_bytes()).hexdigest(),'elapsed_seconds':time.monotonic()-started}
(B/'normal-or-cost-test.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
