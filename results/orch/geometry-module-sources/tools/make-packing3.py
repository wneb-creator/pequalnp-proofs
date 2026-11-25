from pathlib import Path
import json
p=Path('/tmp/oec/pequalnp-pilot-62')
raw=list(map(int,(p/'singleton-packing-input.txt').read_text().split()))
rows=raw[2:470]
edges=[(1<<((l+d)%13))|(1<<(13+l)) for l in range(13) for d in [0,1,3,9]]
assert set(edges)==set(raw[470:])
coords=[(v,v) for v in range(26)]+[(u,v) for u in range(26) for v in range(u+1,26)]
masks=[(1<<u)|(1<<v) for u,v in coords]
blocks=[(mask,sum(1<<r for r,row in enumerate(rows) if row&mask),sum(1<<e for e,edge in enumerate(edges) if edge&mask)) for mask in masks]
def lit(b):return '⟨'+', '.join(map(str,b))+'⟩'
s='import PEqualNP.Defs\n\nnamespace PEqualNP.Outside.L_meta_1896_aux\n\n'+(p/'packing3-definitions.txt').read_text()+'\nnamespace PackingThree\n\ndef blocks : List Block := [\n  '+',\n  '.join(lit(b) for b in blocks)+']\n\n'
s+='def block (i : Fin 351) : Block := blocks.getD i.val ⟨0, 0, 0⟩\n\n'
s+='def endpoints (i : Fin 351) : Fin 26 × Fin 26 :=\n  (['+', '.join('('+str(u)+', '+str(v)+')' for u,v in coords)+'] : List (Fin 26 × Fin 26)).getD i.val (0, 0)\n\n'
s+=(p/'packing3-vertex-definitions.txt').read_text()
rootsets=[]
for typ in ['two-pair','pairs','singletons']:
 lines=(p/f'packing-capacity3-{typ}-roots.txt').read_text().splitlines()
 roots=[list(map(int,line.split()))[1:] for line in lines[1:]]
 assert len(roots)==int(lines[0])
 rootsets.extend([[masks.index(mask) for mask in root] for root in roots])
s+='def rootIndices (a : Fin 31) : List Nat :=\n  (['+', '.join(str(r) for r in rootsets)+'] : List (List Nat)).getD a.val []\n\n'
s+=(p/'packing3-root-footer.txt').read_text()
Path('/workspace/pequalnp-proofs/results/orch/lemmas/PackingThreeCheck.lean').write_text(s)
(p/'packing3-blocks.json').write_text(json.dumps({'rows':rows,'edges':edges,'coords':coords,'blocks':blocks,'root_indices':rootsets}))
print('SOURCE_BYTES',len(s.encode()))
print('BLOCKS',len(blocks),'ROOTS',len(rootsets))
