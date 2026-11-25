import argparse, json, resource, time
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('--candidate',required=True)
parser.add_argument('--geometry',required=True)
parser.add_argument('--output',required=True)
parser.add_argument('--exhaustive',action='store_true')
args=parser.parse_args()
resource.setrlimit(resource.RLIMIT_AS,(4*1024**3,4*1024**3))
result=json.loads(Path(args.candidate).read_text())
geometry=json.loads(Path(args.geometry).read_text())
points=geometry['points'];lines=geometry['lines'];gates=result['gates']
n=len(points)+len(lines);D={0,1,3,9}
assert all(type(value)is int and 0<=value<13 for value in points+lines)
assert result.get('n',n)==n
assert result.get('output',n+len(gates)-1)==n+len(gates)-1
assert gates
embedding=points+[13+line for line in lines]
assert len(set(embedding))==n
assert all(all((point+line)%13 not in D for point in points) for line in range(13) if line not in lines)
assert all(op in(0,1) and 0<=a<n+j and 0<=b<n+j for j,(op,a,b)in enumerate(gates))
def mapped(wire):return embedding[wire] if wire<n else 26+wire-n
full=[[op,mapped(a),mapped(b)]for op,a,b in gates]
output=26+len(full)-1
for point in range(13):
 if point in points:continue
 neighbors=[13+line for line in range(13)if(point+line)%13 in D]
 assert len(neighbors)==4
 wire=neighbors[0]
 for other in neighbors[1:]:
  full.append([1,wire,other]);wire=26+len(full)-1
 full.append([0,point,wire]);star=26+len(full)-1
 full.append([1,output,star]);output=26+len(full)-1
assert len(full)==len(gates)+5*(13-len(points))
assert all(op in(0,1) and 0<=a<26+j and 0<=b<26+j for j,(op,a,b)in enumerate(full))
record={'n':26,'gates':full,'output':output,'gate_count':len(full),'within_posted_bound':len(full)<=63,'partial_gate_count':len(gates),'added_gates':len(full)-len(gates),'point_embedding':points,'line_embedding':lines,'status':'unverified full-plane candidate','lean_verified':False}
path=Path(args.output);path.write_text(json.dumps(record,indent=2))
path.with_suffix('.txt').write_text('\n'.join(' '.join(map(str,gate))for gate in full)+'\n')
incident=[sum(1<<line for line in range(13)if(point+line)%13 in D)for point in range(13)]
positive=[(1<<point)|(1<<(13+line))for point in range(13)for line in range(13)if(point+line)%13 in D]
negative=[]
for point_mask in range(1<<13):
 covered=0
 for point in range(13):
  if(point_mask>>point)&1:covered|=incident[point]
 line_mask=((1<<13)-1)^covered
 closure=sum(int((incident[point]&line_mask)==0)<<point for point in range(13))
 if closure==point_mask:negative.append(point_mask|(line_mask<<13))
assert len(positive)==52 and len(negative)==704
boundary_errors=[]
for index,row in enumerate(positive+negative):
 values=[bool(row&(1<<i))for i in range(26)]
 for op,a,b in full:values.append((values[a]and values[b])if op==0 else(values[a]or values[b]))
 if values[output]!=(index<len(positive)):boundary_errors.append(row)
record.update({'boundary_rows':756,'boundary_mismatches':boundary_errors,'boundary_verified':not boundary_errors,'status':'complete full-plane boundary verified; Lean proof pending'if not boundary_errors else'invalid full-plane candidate'})
path.write_text(json.dumps(record,indent=2))
if args.exhaustive and not boundary_errors:
 started=time.monotonic()
 values=[int(('1'*(1<<i)+'0'*(1<<i))*(1<<(26-i-1)),2)for i in range(26)]
 target=0
 for point in range(13):
  for line in range(13):
   if(point+line)%13 in D:target|=values[point]&values[13+line]
 for op,a,b in full:values.append(values[a]&values[b]if op==0 else values[a]|values[b])
 record.update({'exhaustive_assignments':1<<26,'exhaustive_mismatches':(values[output]^target).bit_count(),'exhaustive_seconds':time.monotonic()-started})
 record['status']='invalid full-plane candidate'if record['exhaustive_mismatches']else'complete exhaustive plane truth verified; Lean proof pending'
 path.write_text(json.dumps(record,indent=2))
print(json.dumps({key:value for key,value in record.items()if key not in ['gates','boundary_mismatches']}),flush=True)
if boundary_errors or record.get('exhaustive_mismatches',0):raise SystemExit(2)
