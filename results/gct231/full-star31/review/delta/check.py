from pathlib import Path
import hashlib,json,re
from collections import Counter

b=Path(__file__).resolve().parent.parent/'library'
old=(b/'FullStar31.lean').read_text()
new=(b/'FullStar31Lean.lean').read_text()
assert hashlib.sha256(old.encode()).hexdigest()=='1d9ce39dfdf8a03b0c818087bd6d243bf209f89840193cf015b9f47cdb55965a'
assert hashlib.sha256(new.encode()).hexdigest()=='4e3efa0b397320b678920ea30e5c1228261ee1d043e99e6134e2d8be60a9e6a3'
oldmeta=json.loads((b/'full-star31-manifest.json').read_text())
meta=json.loads((b/'full-star31-lean-manifest.json').read_text())
assert meta['equations']==oldmeta['equations']
assert meta['source_sha256']==hashlib.sha256(new.encode()).hexdigest()
assert meta['original_single_theorem_source_sha256']==hashlib.sha256(old.encode()).hexdigest()
assert len(new.splitlines())==983 and len(new.encode())==105951
oldprefix=old.split('set_option maxHeartbeats 20000000 in\n',1)[0]
newprefix=new.split('set_option maxHeartbeats 4000000 in\ntheorem certEq400',1)[0]
assert oldprefix[oldprefix.index('namespace '):]==newprefix[newprefix.index('namespace '):]
print('PASS generic prefix byte-identical after import replacement')

oldmain=old.split('theorem full_star_primitive_equations ',1)[1]
newmain=new.split('theorem full_star_primitive_equations ',1)[1]
oldheader,oldbody=oldmain.split(' := by\n',1)
newheader,newbody=newmain.split(' := by\n',1)
assert oldheader==newheader
print('PASS exact final parameter/hypothesis/conjunction statement preserved')
header,claim_text=oldheader.split('(24 : MvPolynomial (Fin 3) ℂ)) :\n',1)
common_header=header+'(24 : MvPolynomial (Fin 3) ℂ)) :\n'
claims=claim_text.split(' ∧\n');assert len(claims)==31
branches=re.findall(r'^  · (.*?)(?=^  · |^\nend )',oldbody,re.M|re.S)
assert len(branches)==31
canon=lambda x:re.sub(r'\s+',' ',x).strip()
names=[]
for index,record in enumerate(meta['equations']):
    name=record['operator'].replace('certD','certEq');names.append(name)
    block=re.search(r'^theorem '+name+r'\b(.*?)(?=\n\n)',new,re.M|re.S).group(1)
    statement,proof=block.split(' := by\n',1)
    assert statement.strip()==(common_header+claims[index]).strip()
    assert canon(proof)==canon(branches[index])
    assert new.count('theorem '+name+' ')==1
    print('PASS helper',index,name,'exact equation and original proof branch')
params=' '.join([f'd{i}' for i in range(9)]+[f'o{i}' for i in range(9)])
proof=newbody.split('\n\nend ',1)[0].strip()
expected='exact ⟨'+',\n    '.join(name+' '+params+' h' for name in names)+'⟩'
assert proof==expected
print('PASS exact31helper conjunction, parameter order and h unchanged')

imports=[line[7:] for line in new.splitlines() if line.startswith('import ')]
assert imports==meta['imports'] and len(imports)==8 and all(i.startswith('Mathlib.') for i in imports)
assert not re.search(r'\bsorry\b|\baxiom\b|native_decide|_root_|"|@\[|^#',new,re.M)
options=re.findall(r'^set_option (\w+) (\d+) in$',new,re.M)
assert Counter(options)=={('maxHeartbeats','1000000'):31,('maxHeartbeats','4000000'):32}
assert new.count('namespace ')==1 and new.rstrip().endswith('end PEqualNP.Outside.L_gct_231_aux')
decls=re.findall(r'^(?:noncomputable )?(?:def|lemma|theorem) (\w+)',new,re.M)
olddecls=re.findall(r'^(?:noncomputable )?(?:def|lemma|theorem) (\w+)',old,re.M)
assert len(decls)==len(set(decls)) and set(decls)==set(olddecls)|set(names)
print('PASS all new declarations exactly31helpers; eight Mathlib imports; format/options clean')
print('PASS source delta review only; no Lean build performed')
print('source_sha256',hashlib.sha256(new.encode()).hexdigest())
print('manifest_sha256',hashlib.sha256((b/'full-star31-lean-manifest.json').read_bytes()).hexdigest())
