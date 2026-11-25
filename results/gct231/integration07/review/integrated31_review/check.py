from pathlib import Path
from collections import Counter
import hashlib,re,json

b=Path(__file__).resolve().parent.parent
oldpath=Path('/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_gct_231.lean')
helperpath=b/'library/FullStar31Individual.lean';newpath=b/'Integrated31.lean'
old=oldpath.read_text();helper=helperpath.read_text();new=newpath.read_text()
hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [oldpath,helperpath,newpath]}
assert hashes[str(oldpath)]=='ad7a60b2d369921dde6ee77592c01d528e6e22dbcc22fc9b063d37fa6dc03572'
assert hashes[str(helperpath)]=='d7bf606daad095450d7e07956c199a4c53a96aab17ad1d3f93196c405f3fe351'
assert hashes[str(newpath)]=='3989f440a6778c2203de025027bf6dd77af6d91a10b1183e32274db49d7fa3b9'
assert len(new.splitlines())==1527 and len(new.encode())==101073
scope='PEqualNP.Outside.L_gct_231_aux'
def inside(text):
    assert text.count('namespace ')==1
    return text.split('namespace '+scope+'\n',1)[1].rsplit('end '+scope,1)[0].strip()
oldinner=inside(old);helperinner=inside(helper);newinner=inside(new)
def declaration(text,name):
    return re.search(r'^noncomputable def '+name+r'\b.*?(?=\n\n)',text,re.M|re.S).group(0)
removed={}
for name in ('starAffine','fullStarMatrix'):
    a=declaration(old,name);c=declaration(helper,name)
    assert a==c
    assert helperinner.count(c)==1
    helperinner=helperinner.replace(c+'\n\n','')
    removed[name]=hashlib.sha256(c.encode()).hexdigest()
assert newinner.startswith(oldinner)
actual_append=newinner[len(oldinner):].strip()
assert re.sub(r'\n{3,}','\n\n',actual_append)==re.sub(r'\n{3,}','\n\n',helperinner.strip())
print('PASS entire old namespace body byte-preserved as candidate prefix')
print('PASS appended helper body exact after deleting only2identical definitions, apart from one blank separator line')

pattern=r'^(?:noncomputable )?(?:def|lemma|theorem|abbrev|opaque|instance|axiom) ([^\s(:]+)'
names_old=re.findall(pattern,old,re.M);names_helper=re.findall(pattern,helper,re.M);names_new=re.findall(pattern,new,re.M)
expected=Counter(names_old)+Counter(names_helper)
for name in removed:expected[name]-=1
assert Counter(names_new)==expected and all(count==1 for count in expected.values())
assert len(re.findall(r'^theorem certEq\d{3} ',new,re.M))==31
assert 'full_star_primitive_equations' not in new
assert not re.search(r'\b(?:sorry|axiom|native_decide|admit)\b|_root_|"|@\[|^#',new,re.M)
assert not re.search(r'^(?:instance|opaque|macro|elab|syntax|initialize|unsafe|partial|set_option (?!max))\b',new,re.M)
imports=[line for line in new.splitlines() if line.startswith('import ')]
expected_imports=[line for line in helper.splitlines() if line.startswith('import ')]+['import PEqualNP.Defs']
assert imports==expected_imports
assert new.startswith('\n'.join(imports)+'\n\n')
options=re.findall(r'^set_option ([\w.]+) (\d+) in$',new,re.M)
assert len(options)==len(re.findall(r'^set_option ',new,re.M))
assert all(name in ('maxHeartbeats','maxRecDepth','synthInstance.maxSize','synthInstance.maxHeartbeats') for name,value in options)
assert not re.search(r'\bimport\b',new.split('\n\n',1)[1])
assert new.rstrip().endswith('end '+scope)
print('PASS all declarations accounted for,31certEq helpers, no fabricated posted main')
print('PASS imports first; scoped auxiliary namespace; no forbidden text/commands')
print('OPTIONS',Counter(options))
print(json.dumps({'source_hashes':hashes,'removed_identical_definition_hashes':removed,'declaration_count':len(names_new)},indent=2))
