from pathlib import Path
import sys,json
D=json.loads(Path('fano-data.json').read_text());n,s=14,26
rows=sorted(D['minimal_true']+D['maximal_false']);A=len(rows)+n+s+1
p=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
positive=set()
for line in Path(sys.argv[1]).read_text().splitlines():
 if line.startswith('v '):positive.update(int(v) for v in line.split()[1:] if int(v)>0)
def pick(kd,j,m):
 q=[a for a in range(m) if p(kd,j,a) in positive]
 if len(q)!=1:raise ValueError(f'Nonunique choice {kd,j,m,q}')
 return q[0]
raw=[]
for j in range(s):raw.append([pick(0,j,3),pick(1,j,n+j+1),pick(2,j,n+j+1)])
output=pick(6,0,n+s+1)
live=set()
def visit(w):
 if w<n or w in live:return
 if w>=n+s:raise ValueError('Output or source names nonexistent wire')
 op,a,b=raw[w-n]
 if op==2:raise ValueError('Constant padding is live')
 if a>=w or b>=w:raise ValueError('Circuit does not read backwards')
 live.add(w);visit(a);visit(b)
visit(output)
ren={i:i for i in range(n)};gates=[]
for j,(op,a,b) in enumerate(raw):
 if n+j not in live:continue
 ren[n+j]=n+len(gates);gates.append({'op':'and' if op==0 else 'or','inputs':[ren[a],ren[b]]})
output=ren[output]
errors=[];truth=[];expected=[]
for r in range(1<<n):
 w=[bool(r>>i&1) for i in range(n)]
 for gate in gates:
  a,b=gate['inputs'];assert a<len(w) and b<len(w)
  w.append(w[a] and w[b] if gate['op']=='and' else w[a] or w[b])
 got=w[output];want=any((r>>a)&1 and (r>>b)&1 for a,b in D['edges'])
 truth.append('1' if got else '0');expected.append('1' if want else '0')
 if got!=want:errors.append(r)
# Joint capped proof-tree multiplicities, exactly as ReadK for a prime edge.
not_read1=[]
for u,v in D['edges']:
 R=[{(1,0)} if i==u else {(0,1)} if i==v else set() for i in range(n)]
 for g in gates:
  a,b=g['inputs']
  if g['op']=='or':value=R[a]|R[b]
  else:value={(min(x+z,2),min(y+t,2)) for x,y in R[a] for z,t in R[b]}
  R.append(value)
 if not any(x<=1 and y<=1 for x,y in R[output]):not_read1.append([u,v])
report={'q':2,'N':7,'edges':D['edges'],'raw_gates':raw,'gates':gates,'output':output,'actual_size':len(gates),'is_ao2':all(g['op'] in ['and','or'] and len(g['inputs'])==2 and all(k<n+j for k in g['inputs']) for j,g in enumerate(gates)),'verified_rows':1<<n,'errors':errors,'actual_truth_table':''.join(truth),'expected_truth_table':''.join(expected),'not_read1_edges':not_read1,'candidate_refutation':len(gates)<=26 and not errors}
Path(sys.argv[2]).write_text(json.dumps(report,indent=2))
print(json.dumps({k:v for k,v in report.items() if k not in ['raw_gates','gates','edges','actual_truth_table','expected_truth_table']}))
