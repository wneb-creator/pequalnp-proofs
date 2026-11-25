from pathlib import Path
import hashlib,json

p=Path(__file__).resolve().parent;repo=Path('/workspace/pequalnp-proofs/results/orch/components2056')
lib=json.loads((repo/'v5-library.json').read_text());mapping=json.loads((p/'v5-nonread-control67.mapping.json').read_text());circuit=json.loads((p/'v5-nonread-control67-circuit.json').read_text())
truth={}
for line in (p/'v5-nonread-control67.sol').read_text().splitlines():
 if line.startswith('v '):
  for token in line[2:].split():
   x=int(token)
   if x:truth[abs(x)]=x>0
edges=[(a,13+b) for a in range(13) for b in range(13) if (a+b)%13 in (0,1,3,9)]
assert mapping['joint_edges']==[list(e) for e in edges]
picked=[i for i,var in enumerate(mapping['joint_edge_selectors']) if truth[var]];assert len(picked)==1
edge=picked[0];chosen={}
for index,var in enumerate(mapping['chosen']):
 if truth[var]:
  q,op,a,b=lib['productions'][index];assert q not in chosen;chosen[q]=(op,a,b)
selected={q for q,var in enumerate(mapping['selected']) if truth[var]}
assert set(chosen)==selected-set(range(26)) and len(chosen)==67
states={i:(sum(1<<j for j,(a,b) in enumerate(edges) if a==i),0,0) if i<13 else (0,sum(1<<j for j,(a,b) in enumerate(edges) if b==i),0) for i in range(26)}
order=[];visiting=set()
def visit(q):
 if q in states:return states[q]
 assert q not in visiting;visiting.add(q);op,a,b=chosen[q];left,right=visit(a),visit(b)
 states[q]=tuple(x|y for x,y in zip(left,right)) if op else (0,0,(left[0]&right[1])|(left[1]&right[0]))
 visiting.remove(q);order.append(q);return states[q]
u,v,g=visit(lib['goal']);assert u==v==0 and not(g>>edge&1)
assert len(order)==67 and order==circuit['selected_profile_order']
for q in selected:
 for index,var in enumerate(mapping['joint_states'][q]):
  actual=var if type(var)is bool else truth[var]
  assert actual==bool(states[q][index]>>edge&1)
wire={i:i for i in range(26)};rebuilt=[]
for q in order:
 op,a,b=chosen[q];rebuilt.append([op,wire[a],wire[b]]);wire[q]=26+len(rebuilt)-1
assert rebuilt==circuit['gates'] and wire[lib['goal']]==circuit['output']
positive=[(1<<a)|(1<<b) for a,b in edges];neighbors=[{b-13 for a,b in edges if a==point} for point in range(13)];negative=[]
for bits in range(1<<13):
 points={i for i in range(13) if bits>>i&1};allowed={j for j in range(13) if all(j not in neighbors[i] for i in points)}
 closure={i for i in range(13) if neighbors[i].isdisjoint(allowed)}
 if points==closure:negative.append(bits|sum(1<<(13+j) for j in allowed))
assert len(negative)==704 and len(set(negative))==704
rows=positive+negative;values=[sum(((r>>i)&1)<<j for j,r in enumerate(rows)) for i in range(26)]
for j,(op,a,b) in enumerate(rebuilt):
 assert 0<=a<26+j and 0<=b<26+j;values.append((values[a]|values[b]) if op else (values[a]&values[b]))
assert values[circuit['output']]==(1<<52)-1
# Independently compare the literal base prefix of the actual target artifact.
base=p/'v5-target63.cnf';target=p/'v5-nonread-target63.cnf';count=0;extra=0
with base.open('rb') as a,target.open('rb') as b:
 base_header=a.readline().split();target_header=b.readline().split()
 for line in a:assert b.readline()==line;count+=1
 for line in b:
  assert line.strip().endswith(b'0');extra+=1
assert count==int(base_header[3]) and count+extra==int(target_header[3])
baseline=json.loads((repo/'control64-circuit.json').read_text());bg=[(sum(1<<j for j,(a,b) in enumerate(edges) if a==i),0,0) if i<13 else (0,sum(1<<j for j,(a,b) in enumerate(edges) if b==i),0) for i in range(26)]
for op,a,b in baseline['gates']:bg.append(tuple(x|y for x,y in zip(bg[a],bg[b])) if op else (0,0,(bg[a][0]&bg[b][1])|(bg[a][1]&bg[b][0])))
assert bg[baseline['output']][2]==(1<<52)-1
negative_run=json.loads((p/'v5-nonread-control64.run.json').read_text());assert negative_run['returncode']==20
report={'verdict':'PASS independent graph/producer/read1 replay and target prefix; full native clauses checked separately','control67_gates':67,'critical_rows':len(rows),'missing_joint_read1_edges':52-g.bit_count(),'selected_missing_edge':edges[edge],'target_base_clauses_unchanged':count,'target_extra_clauses':extra,'baseline64_all52_read1':True,'negative_control_exit':20,'model_sha256':hashlib.sha256((p/'v5-nonread-control67.sol').read_bytes()).hexdigest(),'target_cnf_sha256':hashlib.sha256(target.read_bytes()).hexdigest()}
(p/'nonread-control67-semantic-independent.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
