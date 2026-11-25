import argparse
import json
from pathlib import Path
from extend2056_patch import variable_tables, verified_patch, extend

parser=argparse.ArgumentParser(description='Structurally lift a verified theta-four circuit to its fivepoint patch')
parser.add_argument('--candidate',type=Path,required=True)
parser.add_argument('--cases',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
candidate=json.loads(args.candidate.read_text())
gates=candidate['gates']
if not 1<=len(gates)<=16:raise ValueError('Expected at most16 core gates')
inputs=variable_tables(10);values=inputs[:]
for j,(op,a,b) in enumerate(gates):
 if op not in (0,1) or not 0<=a<10+j or not 0<=b<10+j:raise ValueError('Invalid core gate')
 values.append(values[a]|values[b] if op else values[a]&values[b])
target=0
for i in range(4):
 a=2+2*i;b=a+1
 target|=(inputs[0]&inputs[a])|(inputs[a]&inputs[b])|(inputs[b]&inputs[1])
if values[-1]!=target:raise ValueError('Core does not compute theta-four exactly')
cone={10+len(gates)-1}
for j in reversed(range(len(gates))):
 op,a,b=gates[j]
 if 10+j in cone and op==1:cone.update([a,b])
selected={}
for i in range(4):
 b=3+2*i
 eligible=[j for j,(op,a,c) in enumerate(gates) if 10+j in cone and op==0 and b in (a,c)]
 if not eligible:raise ValueError('No suitable OR-exposed arm-point AND; this lift is inapplicable')
 j=eligible[0]
 if j in selected:raise ValueError('Selected AND gates are not distinct')
 selected[j]=i
case=json.loads(args.cases.read_text())[2]
if case['points']!=[0,1,2,3,9]:raise ValueError('Unexpected fivepoint geometry')
point=lambda p:case['points'].index(p)
line=lambda l:len(case['points'])+case['lines'].index(l)
arm_points=[0,1,3,9];arm_lines=[1,12,11,7]
wiremap=[point(2),line(0)]
for p,l in zip(arm_points,arm_lines):wiremap.extend([line(l),point(p)])
result=[];n=case['ninputs']
for j,(op,a,b) in enumerate(gates):
 aa,bb=wiremap[a],wiremap[b]
 if j in selected:
  i=selected[j];p=arm_points[i];bwire=3+2*i
  private=[l for l in range(13) if (p+l)%13 in (0,1,3,9) and l not in (0,arm_lines[i])]
  if len(private)!=2:raise ValueError('Incorrect private incidence count')
  other=bb if a==bwire else aa
  for l in private:
   result.append([1,other,line(l)]);other=n+len(result)-1
  if a==bwire:bb=other
  else:aa=other
 result.append([op,aa,bb]);wiremap.append(n+len(result)-1)
if len(result)!=len(gates)+8:raise ValueError('Lift gate accounting failed')
checked=verified_patch(case,result)
full,output=extend(case,result)
document={'case':2,'core_gates':len(gates),'core_assignments_verified':1024,'patch_gates':len(result),'patch_assignments_verified':checked,'selected_core_gates':selected,'gates':result,'full_gates':full,'full_output':output,'full_size':len(full),'status':'control only' if len(full)>63 else 'candidate requires full verification and Lean checking'}
args.output.write_text(json.dumps(document,indent=2)+'\n')
args.output.with_suffix('.txt').write_text(''.join(f'{op} {a} {b}\n' for op,a,b in full))
print(f'PASS theta all1024 inputs; patch all{checked} inputs; sizes{len(gates)} -> {len(result)} -> {len(full)}')
