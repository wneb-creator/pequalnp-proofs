from pathlib import Path
import sys,json,hashlib,difflib
root=Path(sys.argv[1] if len(sys.argv)>1 else Path(__file__).resolve().parent)
sha=lambda b:hashlib.sha256(b).hexdigest()
def get(n):
 p=Path(n);assert not p.is_absolute() and '..' not in p.parts
 p=root/p;assert p.is_file() and not p.is_symlink();return p.read_bytes()
m=json.loads(get('manifest.json'));assert {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}==set(m['files'])|{'manifest.json'}
for n,row in m['files'].items():
 b=get(n);assert len(b)==row['bytes'] and sha(b)==row['sha256'] and not b.startswith(b'ELF')
binding=json.loads(get('source-bindings.json'));r=json.loads(get('review/review.json'))
assert sha(get('review/review.json'))=='5146eb7ac9871706deee49391118489790dfaedd3ad7113a73b9d5e256826de3'
assert set(binding)==set(r['bindings'])
for n,row in r['bindings'].items():
 b=binding[n];assert row['bytes']==b['bytes'] and row['sha256']==b['sha256']
 if b['disposition']=='payload':raw=get(b['archive_path']);assert sha(raw)==row['sha256'] and len(raw)==row['bytes']
 else:assert b['disposition']=='omitted_ELF'
p=json.loads(get('portable-reproduction.json'))
def changes(a,b):
 a=a.decode().splitlines(True);b=b.decode().splitlines(True)
 return [(t,a[i:j],b[k:l]) for t,i,j,k,l in difflib.SequenceMatcher(None,a,b,autojunk=False).get_opcodes() if t!='equal']
assert len(changes(get(p['parent141']),get(p['engine'])))==6
assert changes(get(p['parent141']),get(p['engine']))==changes(get(p['parent40']),get(p['shuffle40']))
s=get(p['wrapper_parent']).decode();d=json.loads(get(p['wrapper_derivation']))
for row in d['changes']:assert s.count(row['before'])==1;s=s.replace(row['before'],row['after'])
assert s.encode()==get(p['wrapper']) and len(d['changes'])==2
assert sha(get(p['engine']))==p['source_sha256'] and sha(get(p['wrapper']))==p['wrapper_sha256']
print(json.dumps({'verdict':'PASS_PORTABLE_HASH_INVENTORY_DIRECT_REVIEW_BINDINGS_AND_EXACT_SOURCE_PORT','payloads':len(m['files']),'review_bindings':len(binding),'engine_blocks':6,'wrapper_insertions':2,'workers_started':False}))
