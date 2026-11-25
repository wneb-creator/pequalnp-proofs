from itertools import combinations
import json
n = 8
pairs = list(combinations(range(n), 2))
samples = [0] + [1 << i for i in range(n)] + [(1 << u) | (1 << v) for u, v in pairs]
inputs = [sum(1 << j for j, s in enumerate(samples) if (s >> i) & 1) for i in range(n)]
allones = (1 << len(samples)) - 1
state = {0, allones, *inputs, *(inputs[u] & inputs[v] for u, v in pairs)}
edge_signals = [inputs[2*i] & inputs[2*i+1] for i in range(4)]
e1,e2,e3,e4 = edge_signals
p=inputs[1]&inputs[5]
q1=inputs[0]&inputs[6]
q2=inputs[2]&inputs[4]
target = e1 | e2 | e3 | e4

def components():
    parent = list(range(4))
    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    qualifying = []
    for f in state:
        if f & ~target:
            continue
        members = [i for i,e in enumerate(edge_signals[:4]) if f & e]
        if members:
            for i in members[1:]:
                parent[root(i)] = root(members[0])
            if len(members) > 1:
                qualifying.append(members)
    return len({root(i) for i in range(4)}), sorted(qualifying)

rows=[]
def join(name,a,b):
    global state
    assert a in state and b in state
    before,old = components()
    c=a|b
    state |= {c & s for s in state}
    after,new = components()
    rows.append(dict(name=name,states=len(state),components_before=before,components_after=after,
                     merged_proper_sets=new))
    return c

A=join('A',join('e1_or_p',e1,p),e3)
B=join('B',join('e2_or_p',e2,p),e4)
D1=join('D1',join('e1_or_q1',e1,q1),e2)
D2=join('D2',join('e3_or_q2',e3,q2),e4)
U=join('U',A,B)
assert rows[-1]['components_before']==4 and rows[-1]['components_after']==2
assert U&D1==e1|e2 and U&D2==e3|e4
print(json.dumps({'target_graph':pairs[:0]+[(0,1),(2,3),(4,5),(6,7)],
                  'poison_pairs':[(1,5),(0,6),(2,4)],'input_sigs':inputs,'base':sorted({0,allones,*inputs,*(inputs[u]&inputs[v] for u,v in pairs)}),'edge_sigs':edge_signals,'poison_sigs':[p,q1,q2],'rows':rows},indent=2))
