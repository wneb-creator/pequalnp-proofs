"""Independent finite-field basis, checkpoint, and restart controls."""
from pathlib import Path
import json
import subprocess
import sys
import sympy as s

base=Path(__file__).parent
out=base/'checkpoint-subset/controls'
out.mkdir(exist_ok=True)
runner=base/'run_neogb_checkpoint_subset.py'

def read_input(path):
    lines=path.read_text().splitlines()
    n,m,p,terms=map(int,lines[0].split())
    lengths=list(map(int,lines[1].split()))
    assert len(lengths)==m and sum(lengths)==terms and len(lines)==terms+2
    variables=s.symbols('x:'+str(n))
    polynomials=[];index=2
    for length in lengths:
        table={}
        for line in lines[index:index+length]:
            numerator,denominator,*exponents=map(int,line.split())
            assert len(exponents)==n and all(e>=0 for e in exponents)
            coefficient=numerator*pow(denominator,-1,p)%p
            assert coefficient
            key=tuple(exponents);assert key not in table
            table[key]=coefficient
        polynomials.append(s.Poly.from_dict(table,variables,modulus=p))
        index+=length
    return variables,p,polynomials

def canonical(polys):
    return sorted(tuple(sorted(poly.monic().terms())) for poly in polys if not poly.is_zero)

def read_basis(path,variables,p):
    data=json.loads(path.read_text())
    assert data['characteristic']==p and data['nvars']==len(variables)
    assert sum(map(len,data['basis']))==data['nterms']
    return [s.Poly.from_dict({tuple(e):int(c) for c,e in poly},variables,modulus=p)
            for poly in data['basis']]

def run(label,input_path,base_path,stop):
    prefix=out/label;output=out/(label+'.basis.json')
    command=[sys.executable,str(runner),str(input_path),str(output),str(prefix),
        '--base-input',str(base_path),'--seconds','20','--memory-mib','1024',
        '--output-mib','64','--pairs','32','--threads','1',
        '--checkpoint-seconds','0','--stop-after-round',str(stop)]
    with (out/(label+'.driver.log')).open('w') as log:
        subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
    return json.loads(prefix.with_suffix('.result.json').read_text()),output

summary=[]
for name in ['unit','nonunit','rational']:
    original=(base/f'qqfix-sanity-{name}-p0.in').read_text().splitlines()
    for prime in [101,1009,65537]:
        header=list(map(int,original[0].split()));header[2]=prime
        input_path=out/f'{name}-p{prime}.in'
        input_path.write_text(' '.join(map(str,header))+'\n'+'\n'.join(original[1:])+'\n')
        variables,p,generators=read_input(input_path)
        expected=s.groebner([poly.as_expr() for poly in generators],*variables,
                            modulus=p,order='grevlex')
        expected_basis=canonical(expected.polys)
        full,full_output=run(f'{name}-p{prime}-full',input_path,input_path,0)
        assert full['status']=='COMPLETED'
        assert canonical(read_basis(full_output,variables,p))==expected_basis
        stopped,_=run(f'{name}-p{prime}-stop1',input_path,input_path,1)
        assert stopped['status'] in ('STOPPED_AFTER_CHECKPOINT','COMPLETED')
        snapshot=Path(stopped['checkpoint']['path'])
        sv,sp,rows=read_input(snapshot)
        assert sp==p and tuple(sv)==tuple(variables) and rows[:len(generators)]==generators
        for polynomial in rows[len(generators):]:
            assert expected.reduce(polynomial.as_expr())[1]==0
        resumed,resumed_output=run(f'{name}-p{prime}-resumed',snapshot,input_path,0)
        assert resumed['status']=='COMPLETED'
        assert canonical(read_basis(resumed_output,variables,p))==expected_basis
        assert resumed['checkpoint']['metadata']['original_generators']==len(generators)
        for result in (full,stopped,resumed):
            meta=result['checkpoint']['metadata']
            assert meta['appended_basis_terms'] <= meta['derived_term_budget']
            assert meta['available_basis_rows'] == meta['appended_basis_rows'] + meta['omitted_basis_rows']
            assert meta['available_basis_terms'] == meta['appended_basis_terms'] + meta['omitted_basis_terms']
            checkpoint=Path(result['checkpoint']['path'])
            root=str(checkpoint).rsplit('.s',1)[0]
            retained=list(checkpoint.parent.glob(Path(root).name+'.s*.in'))
            assert 1<=len(retained)<=2
            assert not list(checkpoint.parent.glob(Path(root).name+'*.tmp'))
        record={'name':name,'prime':prime,'expected_basis_size':len(expected_basis),
                'interruption':stopped['status'],
                'verified_checkpoint_rows':len(rows)-len(generators),
                'resumed_matches_original':True}
        summary.append(record)
        print('PASS',record,flush=True)

# An incorrect original-generator prefix must fail before starting the engine.
wrong=out/'wrong-base.in'
lines=(out/'unit-p1009.in').read_text().splitlines()
parts=lines[2].split();parts[0]=str(int(parts[0])+7);lines[2]=' '.join(parts)
wrong.write_text('\n'.join(lines)+'\n')
source=Path(json.loads((out/'unit-p1009-stop1.result.json').read_text())['checkpoint']['path'])
prefix=out/'bad-prefix'
with (out/'bad-prefix.driver.log').open('w') as log:
    result=subprocess.run([sys.executable,str(runner),str(source),
        str(out/'bad-prefix.basis.json'),str(prefix),'--base-input',str(wrong)],
        stdout=log,stderr=subprocess.STDOUT)
assert result.returncode!=0 and not prefix.with_suffix('.log').exists()
print('PASS wrong original-generator prefix rejected before engine start.',flush=True)
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
