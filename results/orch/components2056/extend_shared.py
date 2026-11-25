from pathlib import Path
import hashlib,json

here=Path(__file__).resolve().parent
base_text=(here/'v3-library.json').read_text();base=json.loads(base_text)
extension_text=(here/'shared-dirty-closure-census.json').read_text();extension=json.loads(extension_text)
values=[int(v,16) for v in base['profiles']];productions=set(map(tuple,base['productions']))
for q,op,a,b in extension['novel_productions']:
 assert q>=26 and q not in (a,b) and values[q]==(values[a]|values[b] if op else values[a]&values[b])
 assert (q,op,a,b) not in productions
 productions.add((q,op,a,b))
base['productions']=[list(t) for t in sorted(productions)]
base['extension']={'base_library_sha256':hashlib.sha256(base_text.encode()).hexdigest(),'census_sha256':hashlib.sha256(extension_text.encode()).hexdigest(),'added':194,'retains_all_base_productions':True}
output=json.dumps(base,separators=(',',':'))+'\n'
assert hashlib.sha256(output.encode()).hexdigest()=='0fe46d741695adb40d0c3b7b024d07c6b12ed08a0d9ab921c08565e0f9fd6a7d'
(here/'v4-library.json').write_text(output)
print(json.dumps({'profiles':len(values),'productions':len(productions),'sha256':hashlib.sha256(output.encode()).hexdigest()}))
