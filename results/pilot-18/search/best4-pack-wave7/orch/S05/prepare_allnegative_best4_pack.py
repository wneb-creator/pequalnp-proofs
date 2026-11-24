"""Fresh direct21 pack of immutable one-extra-triple source; no search."""
from pathlib import Path
import json,hashlib,random,time
from prepare_triangle589 import EDGES,NEG,evaluate,write,sha
R=Path('/tmp/oec/pequalnp-pilot-18');H=R/'orch/S05'
SOURCE=R/'orch/MAIN/allnegative-best4/source.json'
PIN='b6da8ac6962d7836f2e5546423f5ed3846b7165fbe1ae47e58b8e470955101b0'
def main():
    start=time.monotonic();assert sha(SOURCE)==PIN;raw=SOURCE.read_bytes();d=json.loads(raw)
    out=H/'allnegative-best4-direct21-v1';out.mkdir(exist_ok=False);(out/'source.json').write_bytes(raw)
    assert d['gate_wire_offset']==13 and d['size']==len(d['gates'])==21
    before=[evaluate(d,m) for m in range(2048)]
    target=[any(m>>a&1 and m>>b&1 for a,b in EDGES) for m in range(2048)]
    expected=[target[m] or bool(m>>2&1 and m>>4&1 and m&1) for m in range(2048)]
    assert [v[d['output']] for v in before]==expected
    assert [m for m in range(2048) if expected[m] and not target[m]]==[21,29,85,149]
    deps=[{w-13 for w in row[1:] if w>=13} for row in d['gates']]
    junk=[5,7];ancestors=set(junk);todo=junk[:]
    while todo:
        for g in deps[todo.pop()]:
            if g not in ancestors:ancestors.add(g);todo.append(g)
    orders=[];entries=[];lines=[];checks=0
    for attempt in range(32):
        rng=random.Random(589134230+attempt);done=set();order=[]
        mode=['original','reverse-ready','early-junk','late-junk'][attempt] if attempt<4 else f'random-{attempt}'
        while len(order)<21:
            ready=[g for g in range(21) if g not in done and deps[g]<=done]
            if attempt==0:g=min(ready)
            elif attempt==1:g=max(ready)
            elif attempt==2:g=min(ready,key=lambda q:(q not in ancestors,q))
            elif attempt==3:g=min(ready,key=lambda q:(q in junk,q))
            else:g=rng.choice(ready)
            order.append(g);done.add(g)
        if order in orders:continue
        orders.append(order);mapping={g:i for i,g in enumerate(order)}
        remap=lambda w:w if w<13 else 13+mapping[w-13]
        seed=dict(inputs=11,gate_wire_offset=13,size=21,gates=[[d['gates'][g][0],*sorted(remap(w) for w in d['gates'][g][1:])] for g in order],output=remap(d['output']))
        truth=14695981039346656037
        for m in range(2048):
            after=evaluate(seed,m);assert after[seed['output']]==expected[m]
            for g in range(21):assert after[13+mapping[g]]==before[m][13+g];checks+=1
            truth=((truth^after[seed['output']])*1099511628211)&((1<<64)-1)
        path=out/f'seed-{len(entries):02d}.json';write(path,seed)
        entries.append(dict(path=str(path),sha256=sha(path),order=mode,new_to_old=order,junk_gates=[mapping[g] for g in junk],full_fn=0,full_fp=4,boundary_fn=0,boundary_fp=3,truth_fnv1a64=truth,all_21_gates_live=True))
        lines.append(f'21 {seed["output"]} 0 4 {truth}');lines.extend(f'{int(op=="and")} {a} {b}' for op,a,b in seed['gates'])
        if len(entries)==8:break
    assert len(entries)==8 and len({tuple(x) for x in orders})==8
    pack=out/'direct-seeds.txt';pack.write_text('COVER_ANNEAL_DIRECT21 1 8\n'+'\n'.join(lines)+'\n')
    tokens=pack.read_text().split();assert tokens[:3]==['COVER_ANNEAL_DIRECT21','1','8'];at=3
    for entry in entries:
        size,output,fn,fp,truth=map(int,tokens[at:at+5]);at+=5;assert (size,fn,fp)==(21,0,4)
        gates=[]
        for g in range(21):
            op,a,b=map(int,tokens[at:at+3]);at+=3;assert op in [0,1] and 0<=a<=b<13+g;gates.append((op,a,b))
        h=14695981039346656037;got_fn=got_fp=0
        for m in range(2048):
            v=[bool(m&(1<<i)) for i in range(11)]+[False,True]
            for op,a,b in gates:v.append((v[a]&v[b]) if op else (v[a]|v[b]))
            assert v[output]==expected[m];got_fn+=target[m] and not v[output];got_fp+=not target[m] and v[output]
            h=((h^v[output])*1099511628211)&((1<<64)-1)
        assert (got_fn,got_fp,h)==(fn,fp,truth)
    assert at==len(tokens) and SOURCE.read_bytes()==raw
    metadata=dict(kind='inexact_positive21_one_extra_triple_direct_seed',candidate_only=True,assigned_shard_exhaustion=False,requires_Lean_proof=True,production_launched=False,count=8,pack_sha256=sha(pack),source_sha256=PIN,preparer_sha256=sha(Path(__file__)),engine_source_sha256='18efdd149487dfee83693dd0781a17316ba0fda9d68c43c6c70c73f96a77250b',engine_binary_sha256='7d802a63b218449bd58178785a917a363edecedace5f65201344804dec3a3870',wrapper_sha256='1e6f24c16faf2948c0aec5e4c300f9114d3e331c5894f191c9e0e7607f8afe8b',raw_validator_sha256='d244bfc58d60560041c5890592f3c2de90905c78fcd058f691b27e7785131401',exact_function='F OR (x0 AND x2 AND x4)',all_16_positive_edges_explicitly_pass=all(expected[(1<<a)|(1<<b)] for a,b in EDGES),full_false_positive_masks=[21,29,85,149],boundary_false_positive_masks=[29,85,149],intermediate_comparisons=checks,decoded_input_checks=2048*len(entries),seeds=entries,elapsed_seconds=time.monotonic()-start)
    write(out/'direct-seeds.json',metadata)
    print(json.dumps({k:metadata[k] for k in ['count','pack_sha256','full_false_positive_masks','boundary_false_positive_masks','intermediate_comparisons','decoded_input_checks','elapsed_seconds']}))
if __name__=='__main__':main()
