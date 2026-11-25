from pathlib import Path
import hashlib,json,subprocess,sys
import sympy as s

base=Path(__file__).parent
x,y=s.symbols('x y')
cases={
    'unit':[x*x+y*y-1,x-y,x+y],
    'nonunit':[x*x-y,y*y-1],
    'rational':[x/s.Integer(2)+y/s.Integer(3),x/s.Integer(4)-y/s.Integer(6)]}
records=[]
for characteristic in [1009]:
    for name,polys in cases.items():
        prefix=base/f'sanity-{name}-p{characteristic}'
        terms=[]
        for expr in polys:
            poly=[]
            for exponents,coefficient in s.Poly(expr,x,y,domain=s.QQ).terms():
                a,b=map(int,coefficient.as_numer_denom())
                if characteristic:
                    a=a*pow(b,-1,characteristic)%characteristic;b=1
                    if a==0:continue
                poly.append((a,b,exponents))
            assert poly and len({t[2] for t in poly})==len(poly)
            terms.append(poly)
        data=f'2 {len(terms)} {characteristic} {sum(map(len,terms))}\n'
        data+=' '.join(str(len(poly)) for poly in terms)+'\n'
        data+=''.join(f'{a} {b} '+ ' '.join(map(str,e))+'\n'
                      for poly in terms for a,b,e in poly)
        infile=prefix.with_suffix('.in');infile.write_text(data)
        outfile=prefix.with_suffix('.basis.json')
        result=subprocess.run([sys.executable,str(base/'run_neogb.py'),str(infile),str(outfile),
                               str(prefix),'--seconds','20','--memory-mib','512'],
                              capture_output=True,text=True,timeout=30)
        prefix.with_suffix('.runner.log').write_text(result.stdout+result.stderr)
        assert result.returncode==0,(name,characteristic,result.returncode)
        record=json.loads(prefix.with_suffix('.result.json').read_text())
        assert record['status']=='COMPLETED',record
        output=json.loads(outfile.read_text())
        assert output['characteristic']==characteristic and output['nvars']==2
        basis=[sum(s.Integer(c)*x**e[0]*y**e[1] for c,e in poly) for poly in output['basis']]
        kwargs={'modulus':characteristic} if characteristic else {'domain':s.QQ}
        expected_polys=[s.Poly(expr,x,y,domain=s.QQ).clear_denoms()[1].as_expr() for expr in polys]
        expected=s.groebner(expected_polys,x,y,order='grevlex',**kwargs)
        normalize=lambda p:tuple(s.Poly(p,x,y,**kwargs).monic().terms())
        assert {normalize(p) for p in basis}=={normalize(p.as_expr()) for p in expected.polys}
        print(name,characteristic,'PASS',record['basis_size'],'basis elements',record['seconds'],'seconds')
        records.append({'case':name,'characteristic':characteristic,'expected_basis':list(map(str,expected.polys)),
                        'status':'PASS','input_sha256':hashlib.sha256(infile.read_bytes()).hexdigest(),
                        'output_sha256':hashlib.sha256(outfile.read_bytes()).hexdigest()})
(base/'sanity-ff-results.json').write_text(json.dumps(records,indent=2)+'\n')
print('ALL_THREE_FINITE_FIELD_SANITY_CASES_PASS')
