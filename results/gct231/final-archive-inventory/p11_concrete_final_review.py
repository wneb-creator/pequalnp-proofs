from pathlib import Path
import re, json, hashlib, datetime, ast
import sympy as s

base=Path('/tmp/oec/pequalnp-pilot-75/gct231')
repo=Path('/workspace/pequalnp-proofs/results/gct231')
P=s.Symbol('P'); records={}
for case,deg,expected,count in [
 (2,[54,82],'548488ed6cdac516542dbe0e73e2a1661d1c3d5e1503b8f10dfe77369402f767',5),
 (3,[67,85],'068e69749d812de901748856d3b1a322b22ba0256005b4b70464be5c0f1aea2c',1)]:
 name=f'C4Case{case}ModularCoprimeList11'; path=base/(name+'.lean'); raw=path.read_bytes(); text=raw.decode()
 assert hashlib.sha256(raw).hexdigest()==expected
 data=json.loads((base/f'c4-case{case}-modular-coprime-p11.json').read_text())
 keys=['original_f','original_g','mod_f','mod_g','mod_a','mod_b','integer_quotient']
 lists=[ast.literal_eval(x) for x in re.findall(r'polynomialOfCoeffs \((\[[^\]]*\]) : List',text)]
 assert len(lists)==7
 pol=[s.Poly(data[k],P,domain=s.ZZ) for k in keys]
 for a,q in zip(lists,pol): assert s.Poly.from_list(a[::-1],P,domain=s.ZZ)==q
 assert [p.degree() for p in pol[:4]]==deg+deg
 for a,m in zip(lists[:2],lists[2:4]): assert [x%11 for x in a]==m and m[-1]!=0
 assert (pol[4]*pol[2]+pol[5]*pol[3]-1-11*pol[6]).is_zero
 for forbidden in ['sorry','admit','native_decide','axiom ']: assert forbidden not in text
 audit=(base/(name+'Audit.lean')).read_text(); assert audit.startswith(text)
 tail=audit[len(text):]; assert len(re.findall(r'^#print axioms ',tail,re.M))==count
 tag='case2-modular-list11-build04' if case==2 else 'case3-modular-concrete-build01'
 status=json.loads((base/(tag+'.run.json')).read_text())
 assert status['status']=='PASS' and status['returncode']==0 and Path(status['input']).name==name+'Audit.lean'
 log=(base/(tag+'.log')).read_text(); axioms=re.findall(r'depends on axioms: \[([^\]]*)\]',log)
 assert len(axioms)==count
 for a in axioms: assert set(x.strip() for x in a.split(','))=={'propext','Classical.choice','Quot.sound'}
 assert 'error:' not in log
 records[str(case)]={'source_sha256':expected,'degrees':deg,'actual_seven_lists_exact':True,'integer_bezout_exact':True,'maps_and_leading_coefficients':True,'audit_exact_source':True,'standard_axiom_queries':count,'status':status}
archive=repo/'c4-case2-modular-coprime-checked'; manifest=archive/'SHA256SUMS'
assert hashlib.sha256(manifest.read_bytes()).hexdigest()=='b9f0b98c5369ec89f1633114dee6e8a6e208af71c452cc298b437dd831d07e3a'
entries={}
for line in manifest.read_text().splitlines():
 h,n=line.split(None,1); n=n.strip().lstrip('*'); entries[n]=h; p=archive/n
 assert p.is_file() and not p.is_symlink(); raw=p.read_bytes(); assert hashlib.sha256(raw).hexdigest()==h
 raw.decode(); assert b'\0' not in raw
assert {str(p.relative_to(archive)) for p in archive.rglob('*') if p.is_file()}==set(entries)|{'SHA256SUMS'}
for n in entries:
 if (base/n).is_file(): assert (archive/n).read_bytes()==(base/n).read_bytes()
records['archive_case2']={'manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'entries':len(entries),'exact_coverage':True,'text_only':True,'scratch_pairing':True}
records['completed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
records['scope']='Concrete degree/map/modular coprimality only; no full norm or chart theorem.'
(base/'p11_concrete_final_review.json').write_text(json.dumps(records,indent=2)+'\n')
print('PASS',json.dumps(records,indent=2))
