import argparse
import hashlib
import json
from pathlib import Path
import sympy as sp

p=argparse.ArgumentParser(description='Convert an exact characteristic-zero polynomial input to sparse neogb terms.')
p.add_argument('input');p.add_argument('output');a=p.parse_args()
source=Path(a.input);rows=source.read_text().splitlines()
characteristic,n,m=map(int,rows[0].split());names=rows[1].split()
assert characteristic==0 and n==len(names) and len(rows)==m+2
variables=sp.symbols(' '.join(names),seq=True);locals_=dict(zip(names,variables))
polys=[sp.Poly(sp.sympify(row.replace('^','**'),locals=locals_),*variables,domain=sp.QQ) for row in rows[2:]]
lengths=[len(poly.terms()) for poly in polys]
assert all(lengths)
out=[f'{n} {m} 0 {sum(lengths)}',' '.join(map(str,lengths))]
for poly in polys:
    for powers,coefficient in poly.terms():
        assert coefficient
        out.append(' '.join(map(str,[coefficient.p,coefficient.q,*powers])))
target=Path(a.output);target.write_text('\n'.join(out)+'\n')
meta={'source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
      'original_variables':names,'companion_variables':['x'+str(i) for i in range(n)],
      'input_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'generators':m,'terms':sum(lengths)}
target.with_suffix('.conversion.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta),flush=True)
