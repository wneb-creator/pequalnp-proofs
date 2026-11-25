from pathlib import Path
import json,sys
job=Path('/tmp/oec/pequalnp-pilot-79');base=sys.argv[1];prime=int(sys.argv[2]);result=json.loads((job/(base+'-p'+str(prime)+'-witness.json')).read_text());assert result['unit'] and result['prime']==prime
witness=result['witness'];lines=(job/(base+'.matrix')).read_text().splitlines();ncols,nrows=map(int,lines[0].split());assert len(witness)==nrows and len(lines)==nrows+1
out=[0]*ncols
for coefficient,line in zip(witness,lines[1:]):
 if not coefficient:continue
 vals=list(map(int,line.split()));assert len(vals)==1+2*vals[0]
 for j in range(vals[0]):out[vals[1+2*j]]=(out[vals[1+2*j]]+coefficient*vals[2+2*j])%prime
assert out==[0]*(ncols-1)+[1]
print(json.dumps({'base':base,'prime':prime,'verified':True,'support':sum(c!=0 for c in witness),'rows':nrows,'columns':ncols}),flush=True)
