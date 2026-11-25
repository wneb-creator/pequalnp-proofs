import argparse,hashlib,json
from pathlib import Path

p=argparse.ArgumentParser()
for name in ['cnf','model','output']:p.add_argument('--'+name,required=True)
a=p.parse_args();cnf=Path(a.cnf);model=Path(a.model)
with cnf.open() as f:
 header=next(line for line in f if line.startswith('p ')).split()
assert header[:2]==['p','cnf'];nvars,nclauses=map(int,header[2:]);values=bytearray(nvars+1);sat=False
for line in model.read_text().splitlines():
 if line.startswith('s '):sat=line.strip()=='s SATISFIABLE'
 if not line.startswith('v '):continue
 for token in line[2:].split():
  literal=int(token)
  if not literal:continue
  var=abs(literal);assert 1<=var<=nvars;value=2 if literal>0 else 1
  assert values[var] in (0,value);values[var]=value
assert sat and all(values[1:])
count=0
with cnf.open() as f:
 for line in f:
  if not line.strip() or line[0] in 'cp':continue
  literals=list(map(int,line.split()));assert literals[-1]==0
  assert all(0<abs(x)<=nvars for x in literals[:-1])
  count+=1;assert any(values[abs(x)]==(2 if x>0 else 1) for x in literals[:-1]),('false clause',count)
assert count==nclauses
report={'verdict':'PASS complete model satisfies every clause','variables':nvars,'clauses':count,'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest(),'model_sha256':hashlib.sha256(model.read_bytes()).hexdigest()}
Path(a.output).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
