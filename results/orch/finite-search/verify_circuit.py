import argparse
import json
from pathlib import Path

def inspect(data):
    n=data['P']+data['L']; gates=data['gates']; edges=data['edges']
    output=data.get('output',n+len(gates)-1)
    inputs=[sum(1<<x for x in range(1<<n) if (x>>i)&1) for i in range(n)]
    values=list(inputs); ancestors=[]; users=[0]*len(gates)
    for j,(op,a,b) in enumerate(gates):
        assert op in ('and','or') and 0<=a<n+j and 0<=b<n+j
        values.append(values[a]&values[b] if op=='and' else values[a]|values[b])
        cone=set()
        for w in (a,b):
            if w>=n:
                cone.add(w-n); cone|=ancestors[w-n]; users[w-n]+=1
        ancestors.append(cone)
    target=0
    for p,l in edges: target |= inputs[p]&inputs[l]
    correct=values[output]==target
    below=[not (v&~target) for v in values[n:]]
    dirty=[j for j,(op,a,b) in enumerate(gates) if op=='and' and not below[j]]
    topform=all(not (gates[i][0]=='and' and below[i]) for j,(op,a,b) in enumerate(gates) if op=='and' for i in ancestors[j])
    dead=set(range(len(gates)))-(ancestors[output-n]|{output-n}) if output>=n else set(range(len(gates)))
    duplicates=[(i,j) for i in range(len(values)) for j in range(max(i+1,n),len(values)) if values[i]==values[j]]
    local=[]
    for j,(op,a,b) in enumerate(gates):
        for child,other in ((a,b),(b,a)):
            if child<n: continue
            k=child-n
            if users[k]!=1 or gates[k][0]!=op: continue
            for grandchild in gates[k][1:]:
                v=values[grandchild]&values[other] if op=='and' else values[grandchild]|values[other]
                if v==values[n+j]: local.append({'parent':j,'private_child':k,'replacement_input':grandchild})
    failed=[]; vectors_by_edge=[]
    for p,l in edges:
        vectors=[{(1,0)} if i==p else {(0,1)} if i==l else set() for i in range(n)]
        for op,a,b in gates:
            vectors.append(vectors[a]|vectors[b] if op=='or' else {(min(3,x+y),min(3,u+v)) for x,u in vectors[a] for y,v in vectors[b]})
        vv=sorted(vectors[output]); vectors_by_edge.append({'edge':[p,l],'vectors':vv})
        if not any(x<=2 and y<=2 for x,y in vv): failed.append([p,l])
    return {'function_correct_all_assignments':correct,'assignments':1<<n,'size':len(gates),'dead_gates':sorted(dead),'semantic_duplicates':duplicates,'topform':topform,'dirty_and_gates':dirty,'local_private_same_operation_deletions':local,'failed_read2_edges':failed,'edge_vectors':vectors_by_edge}

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('input'); a=p.parse_args()
    print(json.dumps(inspect(json.loads(Path(a.input).read_text())),indent=2))
