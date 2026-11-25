from pathlib import Path
import json,subprocess,sys
import sympy as s
base=Path(__file__).resolve().parent
out=base/'vector-controls'
out.mkdir(exist_ok=True)
records=[]
def run_case(name,infile,pairs):
    data=list(map(int,infile.read_text().split()))
    n,m,p,terms=data[:4];lengths=data[4:4+m];pos=4+m
    variables=s.symbols('x:'+str(n))
    polys=[]
    for length in lengths:
        expr=0;seen=set()
        for _ in range(length):
            num,den=data[pos:pos+2];pos+=2
            powers=tuple(data[pos:pos+n]);pos+=n
            assert powers not in seen
            seen.add(powers)
            expr+=s.Rational(num,den)*s.prod(v**e for v,e in zip(variables,powers))
        polys.append(expr)
    assert pos==len(data) and sum(lengths)==terms
    prefix=out/name;basisfile=out/(name+'.basis.json')
    cmd=[sys.executable,str(base/'run_neogb_native.py'),str(infile),str(basisfile),str(prefix),
         '--seconds','20','--memory-mib','512','--pairs',str(pairs),'--threads',str(threads)]
    result=subprocess.run(cmd,capture_output=True,text=True,timeout=30)
    prefix.with_suffix('.runner.log').write_text(result.stdout+result.stderr)
    assert result.returncode==0,(name,result.stderr)
    meta=json.loads(prefix.with_suffix('.result.json').read_text())
    assert meta['status']=='COMPLETED',meta
    exported=json.loads(basisfile.read_text())
    assert exported['characteristic']==p and exported['nvars']==n
    assert sum(map(len,exported['basis']))==exported['nterms']
    actual=[sum(s.Integer(c)*s.prod(v**e for v,e in zip(variables,powers)) for c,powers in poly)
            for poly in exported['basis']]
    kwargs={'modulus':p} if p else {'domain':s.QQ}
    expected=s.groebner(polys,*variables,order='grevlex',**kwargs)
    normalize=lambda f:tuple(s.Poly(f,*variables,**kwargs).monic().terms())
    assert {normalize(f) for f in actual}=={normalize(f.as_expr()) for f in expected.polys}
    expected_unit=list(expected)==[1]
    assert meta['unit_basis']==expected_unit
    records.append({'name':name,'characteristic':p,'pairs_per_round':pairs,'basis_size':len(actual),'unit':expected_unit})
    print(name,'PASS','basis_size',len(actual),'unit',expected_unit,flush=True)

x,y=s.symbols('x y')
f=sum(x**i*y**j for i in range(9) for j in range(9))
polys=[f,2*f+1]
terms=[s.Poly(g,x,y,domain=s.QQ).terms() for g in polys]
for p in (0,101,1009,65537,2147483647):
 text=f'2 2 {p} 162\n81 81\n'
 for poly in terms:
  for exponents,coefficient in poly:
   text+=str(coefficient)+' 1 '+' '.join(map(str,exponents))+'\n'
 infile=out/('wide-p'+str(p)+'.in');infile.write_text(text)
 for threads in (1,3):
  run_case('wide-p'+str(p)+'-t'+str(threads),infile,1)
(out/'results.json').write_text(json.dumps(records,indent=2)+'\n')
print('ALL_TEN_WIDE_ROW_NATIVE_CONTROLS_PASS')
