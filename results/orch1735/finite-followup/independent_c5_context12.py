from pathlib import Path
import json
source=Path('/workspace/pequalnp-proofs/results/orch1735/status-review/c5-context-essential12.json');d=json.loads(source.read_text());n=d['n'];gates=d['gates'];edges={tuple(sorted(e)) for e in d['graph_edges']};F=[any(mask>>a&1 and mask>>b&1 for a,b in edges) for mask in range(1<<n)]
def semantics(gs,bypass=None):
 vals=[[bool(mask>>i&1) for mask in range(1<<n)] for i in range(n)]
 for j,(op,a,b) in enumerate(gs):
  assert op in ['and','or'] and 0<=a<n+j and 0<=b<n+j
  vals.append(vals[bypass[1]] if bypass and j==bypass[0] else [x and y if op=='and' else x or y for x,y in zip(vals[a],vals[b])])
 return vals
vals=semantics(gates);assert vals[-1]==F;clean=[j for j,g in enumerate(gates) if g[0]=='and' and all(not x or f for x,f in zip(vals[n+j],F))];assert clean==[11]
anc=[set() for _ in range(n)];supports=[{i} for i in range(n)]
for j,(op,a,b) in enumerate(gates):anc.append(anc[a]|anc[b]|({a-n} if a>=n else set())|({b-n} if b>=n else set()));supports.append(supports[a]|supports[b] if op=='or' else set())
assert all(i not in anc[n+j] for i in clean for j,g in enumerate(gates) if g[0]=='and')
star={tuple(sorted((a,b))) for j in clean for a in supports[gates[j][1]] for b in supports[gates[j][2]]};ustar=sorted(edges-star);assert len(ustar)==5
preserving=[];checks=0
for j in range(len(gates)):
 for q in range(n+j):
  checks+=1
  if semantics(gates,(j,q))[-1]==F:preserving.append((j,q))
assert checks==126 and not preserving
comparison=[['or',1,4],['and',0,5],['or',1,3],['and',2,7],['and',3,4],['or',6,8],['or',9,10]];assert semantics(comparison)[-1]==F
print(json.dumps({'source':str(source),'full_rows':32,'legal_gates':12,'clean_ANDs':clean,'TopForm':True,'Ustar':ustar,'earlier_wire_replacements_checked':checks,'preserving_replacements':preserving,'seven_gate_comparison':comparison,'verdict':'PASS: all claims independently verified; nonleast despite every earlier-wire replacement changing output'},indent=2))
