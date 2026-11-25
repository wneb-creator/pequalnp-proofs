from pathlib import Path
import json
j=Path('/tmp/oec/pequalnp-pilot-79')
a=json.loads((j/'meta3773-cgp-79060-140-best.json.near-unproductive').read_text());b=json.loads((j/'meta3773-cgp-79002-100-best.json').read_text())
g=[x.copy()for x in a['gates']];offset=len(g)
for op,x,y in b['gates']:g.append([op,x+offset if x>=26 else x,y+offset if y>=26 else y])
g.append([1,a['output'],a['output']]);assert len(g)==128
for i,(op,x,y)in enumerate(g):assert op in(0,1)and 0<=x<26+i and 0<=y<26+i
assert g[0]==[1,0,1]
(j/'meta3773-warm-over63-library64.txt').write_text(str(len(g))+'\n'+'\n'.join(' '.join(map(str,x))for x in g)+'\n')
print(json.dumps({'genotype_gates':len(g),'output':25+len(g),'active_base':len(a['gates']),'inactive_library':len(b['gates']),'output_function':'same as first overapprox circuit; explicit identity wrapper'}))
