import json
import pathlib

HERE=pathlib.Path(__file__).resolve().parent
parent=json.loads((HERE/'four-owner-gadgets.json').read_text())[0]
degree={line:sum(b==line for _,b in parent['edges']) for line in range(4,parent['raw_inputs'])}
private=[line for line,deg in degree.items() if deg==1]
assert len(private)==4
kept=[i for i in range(parent['raw_inputs']) if i not in private]
ren={old:new for new,old in enumerate(kept)}
edges=[[ren[a],ren[b]] for a,b in parent['edges'] if b not in private]
features=[];seen=set();feature_reduction=[]
for old,feature in enumerate(parent['features']):
    parts=tuple(sorted(ren[i] for i in feature['raw_indices'] if i not in private))
    if not parts:feature_reduction.append({'old_feature':old,'kind':'zero'});continue
    if len(parts)==1:feature_reduction.append({'old_feature':old,'kind':'raw_alias','raw':parts[0]});continue
    if parts not in seen:seen.add(parts);features.append(list(parts))
    feature_reduction.append({'old_feature':old,'kind':'feature','feature':features.index(list(parts))})
assert len(kept)==10 and len(edges)==12 and len(features)==3
negatives=[]
for mask in range(1<<10):
    if any(mask>>a&1 and mask>>b&1 for a,b in edges):continue
    if all(any((mask|1<<v)>>a&1 and (mask|1<<v)>>b&1 for a,b in edges)
           for v in range(10) if not(mask>>v&1)):
        negatives.append(mask)
assert len(negatives)==12
raw_tests=[[(1<<a)|(1<<b),1] for a,b in edges]+[[x,0] for x in negatives]
tests=[]
for raw,label in raw_tests:
    available=raw
    for i,f in enumerate(features):
        if any(raw>>v&1 for v in f):available|=1<<(10+i)
    tests.append([available,label])
data=dict(name='four_owner_private_zero_diagnostic',raw_inputs=10,inputs=13,max_gates=14,
          input_original=[parent['input_original'][i] for i in kept],edges=edges,
          features=[{'raw_indices':f} for f in features],raw_tests=raw_tests,tests=tests,
          restricted_original_lines=[parent['input_original'][i] for i in private],
          parent_case=parent['name'],feature_reduction=feature_reduction,
          sufficient_for_full63=False,
          necessity_status='Requires a proof that restricting four private inputs removes at least four paid gates.',
          restoration_status='A kernel witness alone does not restore the four private-line terms within the full budget.')
(HERE/'four-owner-private-zero-kernel.json').write_text(json.dumps(data,indent=2)+'\n')
print(dict(raw_inputs=10,features=features,tests=len(tests),target=14,necessity_status=data['necessity_status']))
