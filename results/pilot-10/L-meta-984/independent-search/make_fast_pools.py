from pathlib import Path
import json,hashlib
p=Path(__file__).resolve().parent;reports=[]
for i in range(31):
 pool=json.loads((p/f'score_pool_{i}.json').read_text());codes=pool['codes']
 tuples=[[(code>>(10*j))&1023 for j in range(6)] for code in codes]
 coords=sorted({c for t in tuples for c in t});width=max(1,(len(coords)-1).bit_length());rank={c:j for j,c in enumerate(coords)}
 packed=[sum(rank[c]<<(width*j) for j,c in enumerate(t)) for t in tuples]
 assert all([coords[(z>>(width*j))&((1<<width)-1)] for j in range(6)]==t for z,t in zip(packed,tuples))
 assert all(all(c>=pool['k'] for c in t[:3]) and all(c<pool['k'] for c in t[3:]) for t in tuples)
 report={'graph':i,'k':pool['k'],'coordinate_array':coords,'rank_width':width,'rank_codes':packed,'original_score_codes':codes,'goal_score_per_code':3,'validation':'Every decoded rank tuple maps exactly to the original six coordinates; every first triple lies in positive half and every last triple in negative half.','source_pool_sha256':hashlib.sha256((p/f'score_pool_{i}.json').read_bytes()).hexdigest()}
 data=json.dumps(report,indent=2)+'\n';destination=p/f'fast_pool_{i}.json'
 if destination.exists():assert destination.read_text()==data
 else:destination.write_text(data)
 reports.append({'graph':i,'coordinates':len(coords),'rank_width':width,'codes':len(codes)})
data=json.dumps(reports,indent=2)+'\n';destination=p/'fast_pool_summary.json'
if destination.exists():assert destination.read_text()==data
else:destination.write_text(data)
print(json.dumps({'graphs':31,'max_coordinates':max(r['coordinates'] for r in reports),'rank_widths':sorted(set(r['rank_width'] for r in reports)),'all_coordinate_mappings_verified':True,'existing_bytes_unchanged':True}))
