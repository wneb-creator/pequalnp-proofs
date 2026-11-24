from pathlib import Path
import json
base=Path('/tmp/oec/pequalnp-pilot-42/sat')
vals=[256463372304,8521482511360,14003410187716736,55389823206179104,155696362464215096,218994303131713984,183565875465424384,229736628136996864,270286071508729856,288160007409369088,192860064594267704,288166778660192704,283797140973809664]
def readmodel(p):
 ls=p.read_text().splitlines()
 if 's SATISFIABLE' not in ls:return None
 return {abs(x):x>0 for l in ls if l.startswith('v ') for x in map(int,l[2:].split()) if x}
for p in base.glob('*witness*.txt'):
 if 'free-and' in p.name:continue
 model=readmodel(p)
 if model is None:continue
 out=vals.copy();circ=[]
 if p.name.startswith('complete'):
  block=129 if p.name.startswith('complete24') else 231
  for i in range(14):
   a=next(j for j in range(28) if model[2+block*i+j]);b=next(j for j in range(28) if model[30+block*i+j]);o=model[1+block*i]
   av=out[a] if a<len(out) else 0;bv=out[b] if b<len(out) else 0
   circ.append([o,a,b]);out.append(av|bv if o else av&bv)
 else:
  ns=json.loads((base/'vars-14.json').read_text())
  for k in range(13,27):
   a=next(j for j in range(k-1) if model[ns[f'a{k}_{j}']]);b=next(j for j in range(1,k) if model[ns[f'b{k}_{j}']]);o=model[ns[f'o{k}']]
   circ.append([o,a,b]);out.append(out[a]|out[b] if o else out[a]&out[b])
 print(p.name,'output',out[-1],'valid',out[-1]==1764784,circ)
 (base/(p.stem+'.json')).write_text(json.dumps(circ))
