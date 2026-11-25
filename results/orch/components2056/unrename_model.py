import argparse,hashlib,json
from pathlib import Path

p=argparse.ArgumentParser()
for option in ['phase','model','output']:p.add_argument('--'+option,required=True)
a=p.parse_args();phase_path=Path(a.phase);phase=json.loads(phase_path.read_text());mask=(phase_path.parent/phase['mask_name']).read_bytes()
assert hashlib.sha256(mask).hexdigest()==phase['mask_sha256'] and len(mask)==(phase['variables']+7)//8
with Path(a.model).open() as src,Path(a.output).open('w') as out:
 for line in src:
  if not line.startswith('v '):out.write(line);continue
  converted=[]
  for token in line[2:].split():
   literal=int(token)
   if not literal:converted.append(0);continue
   var=abs(literal);assert 1<=var<=phase['variables']
   flip=mask[(var-1)//8]>>((var-1)%8)&1
   converted.append(-literal if flip else literal)
  out.write('v '+' '.join(map(str,converted))+'\n')
print(json.dumps({'variables':phase['variables'],'output_sha256':hashlib.sha256(Path(a.output).read_bytes()).hexdigest()}))
