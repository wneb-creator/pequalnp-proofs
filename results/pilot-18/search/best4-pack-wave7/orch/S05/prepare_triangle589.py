"""Finite triangle-template construction and direct21 pack; no production search."""
from pathlib import Path
import hashlib, json, itertools, time

ROOT=Path('/tmp/oec/pequalnp-pilot-18')
HERE=ROOT/'orch/S05'
EDGES=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
NEG=[15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,d):
    with p.open('x') as f: json.dump(d,f,indent=2);f.write('\n')
def evaluate(d,m):
    v=[bool(m>>i&1) for i in range(11)]
    if d['gate_wire_offset']==13:v += [False,True]
    for op,a,b in d['gates']:v.append(v[a] and v[b] if op=='and' else v[a] or v[b])
    return v
def construct(a,b,c):
    gates=[];memo={}
    def op(t,x,y):
        key=(t,*sorted((x,y)))
        if key not in memo:memo[key]=11+len(gates);gates.append(list(key))
        return memo[key]
    def join(t,*ws):
        z=ws[0]
        for w in ws[1:]:z=op(t,z,w)
        return z
    # Template (a+b+f)*(c+(a+e)*(b+d)) covers a triangle and its grouped leaves,
    # plus the product of the three leaf groups. d belongs to a, e to b, f to c.
    leaf={5:2,8:join('or',1,4),9:join('or',0,7)}
    upper=join('or',a,b,leaf[c])
    dirty=op('and',op('or',a,leaf[b]),op('or',b,leaf[a]))
    triangle=op('and',upper,op('or',c,dirty))
    residual=join('or',op('and',1,4),op('and',3,op('or',6,7)),op('and',6,7),op('and',10,join('or',0,2,4,6)))
    output=op('or',triangle,residual)
    return dict(inputs=11,gate_wire_offset=11,gate_count=len(gates),gates=gates,output=output)
def main():
    started=time.monotonic();out=HERE/'triangle589-direct21-v1';out.mkdir(exist_ok=False)
    original=HERE/'triangle589-positive21.json'
    assert sha(original)=='2d99849c19f69c76b232e4d55ce487638721291dac4faea3e82dc3274414bfbe'
    target=[any(m>>a&1 and m>>b&1 for a,b in EDGES) for m in range(2048)]
    expected=[target[m] or bool(m>>2&1 and (m&129) and (m&18)) for m in range(2048)]
    original_data=json.loads(original.read_text())
    assert [evaluate(original_data,m)[original_data['output']] for m in range(2048)]==expected
    bases=[('original',original_data)]+[(f'centers-{a}{b}{c}',construct(a,b,c)) for a,b,c in [(8,9,5),(5,9,8),(5,8,9)]]
    entries=[];lines=[];checks=0
    for label,data in bases:
        assert len(data['gates'])==21
        before=[evaluate(data,m) for m in range(2048)]
        assert [v[data['output']] for v in before]==expected
        write(out/(label+'-original.json'),data)
        deps=[{w-11 for w in g[1:] if w>=11} for g in data['gates']]
        junk=[g for g,(op,a,b) in enumerate(data['gates']) if op=='and' and any(not target[m] and before[m][11+g] for m in range(2048))]
        ancestors=set(junk);todo=list(junk)
        while todo:
            for g in deps[todo.pop()]:
                if g not in ancestors:ancestors.add(g);todo.append(g)
        for mode in ['original','reverse-ready','early-junk','late-junk']:
            done=set();order=[]
            while len(done)<21:
                ready=[g for g in range(21) if g not in done and deps[g]<=done]
                key={'original':lambda g:g,'reverse-ready':lambda g:-g,'early-junk':lambda g:(g not in ancestors,g),'late-junk':lambda g:(g in junk,g)}[mode]
                g=min(ready,key=key);done.add(g);order.append(g)
            mapping={g:i for i,g in enumerate(order)}
            remap=lambda w:w if w<11 else 13+mapping[w-11]
            seed=dict(inputs=11,gate_wire_offset=13,size=21,gates=[[data['gates'][g][0],*sorted(remap(w) for w in data['gates'][g][1:])] for g in order],output=remap(data['output']))
            fn=[];fp=[];truth=14695981039346656037
            for m in range(2048):
                after=evaluate(seed,m);value=after[seed['output']]
                assert value==expected[m]
                for g in range(21):assert before[m][11+g]==after[13+mapping[g]];checks+=1
                if value and not target[m]:fp.append(m)
                if target[m] and not value:fn.append(m)
                truth=((truth^value)*1099511628211)&((1<<64)-1)
            assert not fn and len(fp)==10
            path=out/f'seed-{len(entries):02d}.json';write(path,seed)
            entries.append(dict(path=str(path),sha256=sha(path),base=label,order=mode,new_to_old=order,junk_gates=[mapping[g] for g in junk],full_fn=0,full_fp=10,boundary_fn=0,boundary_fp=6,truth_fnv1a64=truth))
            lines.append(f'21 {seed["output"]} 0 10 {truth}');lines.extend(f'{int(op=="and")} {a} {b}' for op,a,b in seed['gates'])
    pack=out/'direct-seeds.txt';pack.write_text(f'COVER_ANNEAL_DIRECT21 1 {len(entries)}\n'+'\n'.join(lines)+'\n')
    # Decode the bytes independently of the seed dictionaries and validate all inputs again.
    tokens=pack.read_text().split();assert tokens[:3]==['COVER_ANNEAL_DIRECT21','1',str(len(entries))];at=3
    for entry in entries:
        size,output,fn,fp,truth=map(int,tokens[at:at+5]);at+=5;assert size==21
        gates=[]
        for g in range(21):
            op,a,b=map(int,tokens[at:at+3]);at+=3;assert op in (0,1) and 0<=a<=b<13+g;gates.append((op,a,b))
        actual=[]
        for m in range(2048):
            v=[bool(m&(1<<i)) for i in range(11)]+[False,True]
            for op,a,b in gates:v.append((v[a]&v[b]) if op else (v[a]|v[b]))
            actual.append(v[output])
        assert actual==expected
    assert at==len(tokens)
    fp=[m for m in range(2048) if expected[m] and not target[m]]
    result=dict(kind='triangle589_inexact_positive21_direct_seed',exact_target=False,lean_proof=False,production_launched=False,source_sha256=sha(original),preparer_sha256=sha(Path(__file__)),pack_sha256=sha(pack),engine_source_sha256='e1a686c19d09439595cdfbf89baf42ff5d1dbfff8949e505b53b999d683ec077',engine_binary_sha256='cace36645bc4a5c827f5a221965ccdef78c554e6d940d69645da292be6c0b51a',wrapper_sha256='1e6f24c16faf2948c0aec5e4c300f9114d3e331c5894f191c9e0e7607f8afe8b',raw_validator_sha256='d244bfc58d60560041c5890592f3c2de90905c78fcd058f691b27e7785131401',count=len(entries),all_target_edges_explicitly_pass=all(expected[(1<<a)|(1<<b)] for a,b in EDGES),full_false_positive_masks=fp,minimal_extra_masks=[m for m in fp if not any(n!=m and n&m==n for n in fp)],boundary_false_positive_masks=[m for m in NEG if expected[m]],intermediate_comparisons=checks,decoded_pack_input_checks=2048*len(entries),seeds=entries,elapsed_seconds=time.monotonic()-started)
    write(out/'direct-seeds.json',result)
    print(json.dumps({k:result[k] for k in ['count','pack_sha256','full_false_positive_masks','boundary_false_positive_masks','intermediate_comparisons','decoded_pack_input_checks','elapsed_seconds']}))
if __name__=='__main__':main()
