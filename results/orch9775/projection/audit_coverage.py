from pathlib import Path
import json,re,ast,hashlib
base=Path('results/orch9775');ws=base/'lemmas/WeightClassification.lean';gs=base/'lemmas/UpstreamGraph.lean';orb=base/'search/compact-orbits.json';cs=base/'search/compact-certificates/summary.json'
def leanlist(p,name):
 line=next(l for l in p.read_text().splitlines() if l.startswith('def '+name+' '));return ast.literal_eval(line.split(':=',1)[1].strip())
E=leanlist(gs,'edges');expected=[(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)];assert E==expected
weights=leanlist(ws,'weights');ten=leanlist(ws,'tenMasks');eleven=leanlist(ws,'elevenMasks')
def possible(cap,m):return all(not(m>>a&1 and m>>b&1) for a,b in E) and 14<=m.bit_count()+cap and all(k&m!=k or 14+w<=m.bit_count()+cap for k,w in weights)
assert [m for m in range(16384) if possible(9,m)]==[]
assert [m for m in range(16384) if possible(10,m)]==ten
assert [m for m in range(16384) if possible(11,m)]==eleven
od=json.loads(orb.read_text());perms=od['permutations'];orbits={int(k):v for k,v in od['orbits'].items()};edges={frozenset(e)for e in E}
for p in perms:
 assert sorted(p)==list(range(14));assert{frozenset((p[a],p[b]))for a,b in E}==edges
for p in perms:
 for q in perms:assert[p[q[i]]for i in range(14)]in perms
def move(m,p):return sum(1<<p[i] for i in range(14) if m>>i&1)
seen=[];transport=[]
for rep,vals in orbits.items():
 assert sorted({move(rep,p)for p in perms})==vals
 for m in vals:
  idx=next(j for j,p in enumerate(perms) if move(m,p)==rep)
  assert move(m,perms[idx])==rep
  transport.append({'source':m,'representative':rep,'permutation_index':idx});seen.append(m)
assert sorted(seen)==eleven and len(set(seen))==117
summary=json.loads(cs.read_text());assert{r['I']for r in summary}==set(orbits)-{127}
for r in summary:assert r['k']==r['I'].bit_count()-3
results=[]
for m in ten:
 kind='weak'if m in [1290,8488]else'paired';p=Path('/tmp/oec/pequalnp-pilot-103/orch9775')/f'{kind}-{m}.result.json';r=json.loads(p.read_text());assert r['I']==m and r['k']==m.bit_count()-4 and r['exit_code']==20;results.append(r)
checked=[]
for m in eleven:
 p=Path('/tmp/oec/pequalnp-pilot-103/orch9775/compact-batch')/f'case-{m}.result.json';r=json.loads(p.read_text());assert r['I']==m and r['k']==m.bit_count()-3
 assert r['exit_code']==(10 if m in[127,16256] else 20);checked.append(r)
report={'verdict':'PASS for exhaustive finite coverage/arithmetic/graph automorphisms; full Lean assembly pending','graph_edges':E,'weight_rows':len(weights),'all_masks_tested':16384,'cap9_survivors':0,'cap10_survivors':ten,'cap10_residual_counts':{str(m):m.bit_count()-4 for m in ten},'cap11_survivors':len(eleven),'automorphisms_verified':len(perms),'orbits':len(orbits),'certificate_orbits':len(summary),'side_masks':[127,16256],'transport':transport,'cap10_solver_results':results,'cap11_solver_counts':{'UNSAT':115,'SAT_handled_by_side_lemma':2},'hashes':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in[ws,gs,orb,cs]},'caveat':'Solver UNSAT is evidence only until generated resolution proofs pass Lean; permutation transport theorem not yet supplied.'}
(base/'case-coverage-independent.json').write_text(json.dumps(report,indent=2)+'\n');print({k:v for k,v in report.items() if k not in['transport','hashes','cap10_solver_results','graph_edges']})
