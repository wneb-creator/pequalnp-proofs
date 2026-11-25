from pathlib import Path
import sys,json,hashlib,datetime
base=Path(sys.argv[1]);reports=[]
inputs=[sum(1<<mask for mask in range(16384) if mask&(1<<i)) for i in range(14)]
def readcnf(tag,m):
 with (base/(tag+'.cnf')).open() as f:
  assert f.readline().split()==['p','cnf',str(m['variables']),str(m['clauses'])]
  cs=[]
  for line in f:
   xs=list(map(int,line.split()));assert xs[-1]==0;cs.append(tuple(xs[:-1]))
 assert len(cs)==m['clauses'];return cs
for suffix in ['18-target','28-control','-host-control']:
 tag='sat-p14-compact-redundancy'+suffix;oldtag='sat-p14-compact-cross'+suffix
 m=json.loads((base/(tag+'.metadata.json')).read_text());old=json.loads((base/(oldtag+'.metadata.json')).read_text());cs=readcnf(tag,m);oldcs=readcnf(oldtag,old)
 ex=m['positive_redundancy'];assert ex['variable_begin']==old['variables'];assert ex['clause_begin']==old['clauses'];assert cs[:ex['clause_begin']]==oldcs
 stripped={k:v for k,v in m.items() if k not in ['positive_redundancy','variables','clauses']};assert stripped=={k:v for k,v in old.items() if k not in ['variables','clauses']}
 expected=[];newvars=[]
 if ex['enabled']:
  assert m['equality'];assert len(ex['atoms'])==m['cap']
  for atom,rows in zip(m['atoms'],ex['atoms']):
   assert len(rows)==14
   for x,entry in enumerate(rows):
    indices=[i for i,mask in enumerate(m['positive']) if not(mask&(1<<x))];terms=[atom['values'][i] for i in indices];v=entry['out']
    assert entry==dict(label=x,positive_indices=indices,terms=terms,out=v);newvars.append(v)
    expected.append(tuple([-v]+terms));expected.extend([(-t,v) for t in terms]);expected.append((-atom['modes'][1+x],v))
    for consumer in atom['consumers']:
     sx=m['atoms'][consumer['atom']]['slots'][consumer['side']]['primary'][x]
     expected.append((-atom['modes'][0],-consumer['var'],-sx,v))
 assert cs[ex['clause_begin']:]==expected;assert ex['clause_end']==len(cs);assert newvars==list(range(ex['variable_begin']+1,m['variables']+1))
 result=dict(tag=tag,enabled=ex['enabled'],added_variables=len(newvars),added_clauses=len(expected),base_clauses_verified=len(oldcs))
 if suffix=='18-target':reports.append(result);continue
 A={int(k):bool(v) for k,v in json.loads((base/(tag+'.complete-assignment.json')).read_text()).items()};oldA={int(k):bool(v) for k,v in json.loads((base/(oldtag+'.complete-assignment.json')).read_text()).items()};c=json.loads((base/(tag+'.compact-control.json')).read_text())
 assert c==json.loads((base/(oldtag+'.compact-control.json')).read_text());assert {k:A[k] for k in oldA}==oldA;assert set(A)==set(range(1,m['variables']+1))
 for j,cl in enumerate(cs):assert any(A[abs(v)]==(v>0) for v in cl),(tag,j)
 vals=[]
 for j,atom in enumerate(m['atoms']):
  active=j<len(c['atoms']);assert A[atom['active']]==active;ss=[]
  for side,slot in enumerate(atom['slots']):
   selected=c['atoms'][j]['slots'][side] if active else dict(primary=[],prior=[])
   for k,v in enumerate(slot['primary']):assert A[v]==(k in selected['primary'])
   for k,v in enumerate(slot['prior']):assert A[v]==(k in selected['prior'])
   sv=0
   for k in selected['primary']:sv|=inputs[k]
   for k in selected['prior']:assert k<j;sv|=vals[k]
   for row,mask in enumerate(m['tests']):assert A[slot['values'][row]]==bool((sv>>mask)&1)
   ss.append(sv)
  vals.append(ss[0]&ss[1])
  for row,mask in enumerate(m['tests']):assert A[atom['values'][row]]==bool((vals[j]>>mask)&1)
  if ex['enabled']:
   for x,entry in enumerate(ex['atoms'][j]):
    actual=any((vals[j]>>mask)&1 for mask in m['positive'] if not(mask&(1<<x)));assert A[entry['out']]==actual
    if A[atom['modes'][x+1]]:assert actual
    if A[atom['modes'][0]]:
     for con in atom['consumers']:
      if A[con['var']] and A[m['atoms'][con['atom']]['slots'][con['side']]['primary'][x]]:assert actual
 out=0
 for j,v in enumerate(m['final']):assert A[v]==(j in c['final'])
 for j in c['final']:out|=vals[j]
 target=0
 for x,y in m['edges']:target|=inputs[x]&inputs[y]
 assert out==target
 dsout=[]
 for initial,seed in [(0,7),(7,0)]:
  vs=[];ds=[]
  for atom in c['atoms']:
   sv=[];sd=[]
   for slot in atom['slots']:
    sv.append(initial in slot['primary'] or any(vs[k] for k in slot['prior']));sd.append(seed in slot['primary'] or any(ds[k] for k in slot['prior']))
   vs.append(sv[0] and sv[1]);ds.append((sv[0] and sd[1])or(sd[0] and sv[1]))
  d=any(ds[j] for j in c['final']);assert not d;dsout.append(d)
 result.update(all_clauses_checked=len(cs),all_variables_checked=len(A),truth_rows=16384,marked_derivatives=dsout,inactive_suffix=m['cap']-len(c['atoms']));reports.append(result)
report=dict(verdict='PASS',reviewer='constructive_search',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),encoder_sha256=hashlib.sha256((base/'sat-p14-compact-redundancy.py').read_bytes()).hexdigest(),controls=reports,mathematical_scope=['Exact27 Fano reconstruction plus ordinary lower27 justifies function-only deletion. A hosted atom Q occurs physically once in its owning x-proxy. If Q is false on every positive edge omitting x, removal leaves every positive edge unchanged since x is already true on the others; negatives only decrease. At least one OR gate disappears and the x argument remains.','Single-use mode0 has the same deletion inside its sole consuming slot carrying x. A hosting mode with only one logical consumer is also covered. No restriction is imposed on an unrelated label in only one consumer of a twice-used atom.','All prefix metadata and clauses equal the frozen cross variant; all new variables and clauses reconstructed independently. Both complete controls check every CNF clause, selected operands, all16384 truth rows and both marked raw derivatives. The Fano28 control disables this minimal27 cut; hosted matching enables it as a clause control only.'],scope='Encoder and controls only; no SAT outcome or Lean certificate.')
(base/'constructive-redundancy-encoder-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
