from pathlib import Path
import re,json
s=Path('/tmp/oec/pequalnp-pilot-62');m=s/'lean-modules'
original=m/'GeometryCompletenessFull.lean'
if not original.exists(): original.write_text((m/'GeometryCompleteness.lean').read_text())
t=original.read_text();start=t.index('set_option');end=t.rfind('set_option maxRecDepth',0,t.index('lemma masks_classified'))
parts=re.split(r'(?=set_option maxRecDepth 100000 in\n)',t[start:end]);parts=[p for p in parts if p.strip()]
assert len(parts)==64
head='import GeometryMaskData\nimport GeometryCompletenessProofs\n\nnamespace PEqualNP.Outside.L_meta_1896_aux.GeometryComplete\n\n'
tail='end PEqualNP.Outside.L_meta_1896_aux.GeometryComplete\n'
for g in range(8):
 for j,p in enumerate(parts[8*g:8*g+8]):assert f'lemma classified_{8*g+j} :' in p
 (m/f'GeometryCompletenessGroup{g}.lean').write_text(head+''.join(parts[8*g:8*g+8])+tail)
(m/'GeometryCompleteness.lean').write_text(''.join(f'import GeometryCompletenessGroup{g}\n' for g in range(8))+'\nnamespace PEqualNP.Outside.L_meta_1896_aux.GeometryComplete\n\n'+t[end:])
print(json.dumps({'groups':8,'chunks_per_group':8,'original_chunks':len(parts)}))
