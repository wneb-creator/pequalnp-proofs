import argparse
import importlib.util
import json
import random
import time
from pathlib import Path


def load_module(path):
    spec=importlib.util.spec_from_file_location('plane_search',path)
    m=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def all_signatures(gates, base):
    vals=base.INPUTS.copy()
    dx=[int(i==0) for i in range(26)]
    dy=[int(i==13) for i in range(26)]
    for op,a,b in gates:
        va,vb=vals[a],vals[b]
        if op==0:
            vals.append(va|vb)
            dx.append(dx[a]|dx[b])
            dy.append(dy[a]|dy[b])
        else:
            vals.append(va&vb)
            dx.append((((va>>base.PY)&1)&dx[b]) | (dx[a]&((vb>>base.PY)&1)))
            dy.append((((va>>base.PX)&1)&dy[b]) | (dy[a]&((vb>>base.PX)&1)))
    return vals,dx,dy


def valid(gates, base):
    if not gates: return False
    for j,(_,a,b) in enumerate(gates):
        if not (0<=a<b<26+j): return False
    vals,dx,dy=all_signatures(gates,base)
    return vals[-1]==base.WANTED and dx[-1]==dy[-1]==0


def trim(gates, output=None):
    if output is None: output=25+len(gates)
    used={output}
    for j in range(len(gates)-1,-1,-1):
        if 26+j in used: used.update(gates[j][1:])
    ren={i:i for i in range(26)}
    result=[]
    for j,(op,a,b) in enumerate(gates):
        if 26+j not in used: continue
        a,b=ren[a],ren[b]
        if a==b: return None
        result.append((op,min(a,b),max(a,b)))
        ren[26+j]=25+len(result)
    if output<26 or ren[output]!=25+len(result): return None
    return tuple(result)


def compress(gates,base):
    ans=trim(gates)
    if ans is not None and len(ans)<len(gates) and valid(ans,base): return ans,'unused'
    vals,dx,dy=all_signatures(gates,base)
    seen={}
    for w,key in enumerate(zip(vals,dx,dy)):
        for v in seen.get(key,[]):
            if w<26: continue
            new=[]
            alias={w:v}
            legal=True
            for j,(op,a,b) in enumerate(gates):
                while a in alias: a=alias[a]
                while b in alias: b=alias[b]
                if a==b:
                    # OR duplication preserves linear parts; AND duplication is
                    # allowed only when its full trace signature matches the child.
                    out=26+j
                    if op==0 or (vals[out],dx[out],dy[out])==(vals[a],dx[a],dy[a]):
                        alias[out]=a
                        new.append((op,0,1))
                    else:
                        legal=False
                        break
                else: new.append((op,min(a,b),max(a,b)))
            if not legal: continue
            output=25+len(gates)
            while output in alias: output=alias[output]
            ans=trim(tuple(new),output)
            if ans is not None and len(ans)<len(gates) and valid(ans,base): return ans,'signature'
        seen.setdefault(key,[]).append(w)
    return None,None


def mutation(gates,rng):
    g=list(gates)
    kind=rng.randrange(100)
    if kind<28:
        # Associative rotations create neutral moves across binary tree shapes.
        j=rng.randrange(1,len(g))
        op,a,b=g[j]
        if rng.randrange(2): a,b=b,a
        if a<26: return None,'rotation'
        child=a-26
        op2,c,d=g[child]
        if op2!=op or b>=26+child: return None,'rotation'
        if rng.randrange(2): c,d=d,c
        if c==b or d==a: return None,'rotation'
        g[child]=(op,min(c,b),max(c,b))
        g[j]=(op,min(a,d),max(a,d))
        return tuple(g),'rotation'
    if kind<38:
        # Redirect one fanout independently; this exposes output-irrelevant choices.
        j=rng.randrange(len(g))
        op,a,b=g[j]
        if rng.randrange(2): a=rng.randrange(26+j)
        else: b=rng.randrange(26+j)
        if a==b: return None,'edge'
        g[j]=(op,min(a,b),max(a,b))
        return tuple(g),'edge'
    steps=rng.choices([1,2,3,4,6],[60,25,9,5,1])[0]
    for _ in range(steps):
        j=rng.randrange(len(g))
        op,a,b=g[j]
        change=rng.randrange(12)
        if change==0: op^=1
        elif change==1:
            op=rng.randrange(2)
            a,b=rng.sample(range(26+j),2)
        elif rng.randrange(2): a=rng.randrange(26+j)
        else: b=rng.randrange(26+j)
        if a==b: return None,'random'
        g[j]=(op,min(a,b),max(a,b))
    return tuple(g),'random'



def rebuild(nodes,output):
    ren={i:i for i in range(26)}
    result=[]
    visiting=set()
    def visit(w):
        if w in ren:return ren[w]
        if w in visiting: raise ValueError('cycle')
        visiting.add(w)
        op,a,b=nodes[w-26]
        a,b=visit(a),visit(b)
        if a==b: raise ValueError('duplicate operand')
        result.append((op,min(a,b),max(a,b)))
        ren[w]=25+len(result)
        visiting.remove(w)
        return ren[w]
    try:
        out=visit(output)
    except ValueError:return None
    if out!=25+len(result):return None
    return tuple(result)


def expansions(gates,rng):
    choices=[]
    for j,(op,a,b) in enumerate(gates):
        if op!=0:continue
        for child,other in [(a,b),(b,a)]:
            if child>=26 and gates[child-26][0]==1:
                choices.append((j,child,other))
    rng.shuffle(choices)
    for j,child,other in choices:
        _,a,b=gates[child-26]
        if a==other or b==other:continue
        nodes=list(gates)
        first=26+len(nodes)
        nodes.extend([(0,a,other),(0,b,other)])
        nodes[j]=(1,first,first+1)
        result=rebuild(nodes,25+len(gates))
        if result is not None and len(result)==65:yield result


def contractions(gates,rng):
    choices=[]
    for j,(op,a,b) in enumerate(gates):
        if op!=1 or a<26 or b<26:continue
        oa,x,y=gates[a-26];ob,z,t=gates[b-26]
        if oa!=0 or ob!=0:continue
        for common in {x,y}&{z,t}:
            left=y if x==common else x
            right=t if z==common else z
            if left==right:continue
            choices.append((j,common,left,right))
    rng.shuffle(choices)
    for j,common,a,b in choices:
        nodes=list(gates)
        fresh=26+len(nodes)
        nodes.append((1,a,b))
        nodes[j]=(0,common,fresh)
        result=rebuild(nodes,25+len(gates))
        if result is not None and len(result)==64:yield result


def relocate(gates,rng,base):
    for small in contractions(gates,rng):
        if valid(small,base):return small
        for large in expansions(small,rng):
            if valid(large,base):return large
    small=base.star(rng,False,rng.randrange(2)==0)
    for large in expansions(small,rng):
        if valid(large,base):return large
    return None


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--seconds',type=int,default=1800)
    p.add_argument('--seed',type=int,default=640065)
    p.add_argument('--source',type=Path,required=True)
    p.add_argument('--witness',type=Path,required=True)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    base=load_module(a.source)
    rng=random.Random(a.seed)
    gates=tuple(tuple(g) for g in json.loads(a.witness.read_text())['gates'])
    assert len(gates)==65 and valid(gates,base)
    start=time.monotonic(); next_report=start+30; next_restart=start+120
    attempts=accepted=changed=duplicates=0
    seen={gates}; bank=[gates]
    kinds={k:[0,0] for k in ['rotation','edge','random','relocation']}
    print(json.dumps({'start':True,'seed':a.seed,'seconds':a.seconds,
                      'positive_basis':len(base.EDGES),'negative_basis':len(base.INDEPENDENT),
                      'method':'valid65 neutral walk; signatures include boundary values and both derivatives'}),flush=True)
    while time.monotonic()-start<a.seconds:
        attempts+=1
        if attempts % 2000 == 0:
            candidate,kind=relocate(gates,rng,base),'relocation'
        else:
            candidate,kind=mutation(gates,rng)
        kinds[kind][0]+=1
        if candidate is not None and candidate!=gates:
            if valid(candidate,base):
                if len(candidate)<65:
                    payload={'found':True,'reason':'direct relocation compression','seconds':time.monotonic()-start,'attempts':attempts,'gates':candidate,'gate_count':len(candidate),'seed':a.seed}
                    a.out.write_text(json.dumps(payload)+'\n')
                    print(json.dumps({k:v for k,v in payload.items() if k!='gates'}),flush=True)
                    return
                accepted+=1; kinds[kind][1]+=1
                if candidate not in seen:
                    changed+=1; seen.add(candidate)
                    if len(seen)>200000: seen={candidate}
                    if len(bank)<64: bank.append(candidate)
                    elif rng.randrange(50)==0: bank[rng.randrange(len(bank))]=candidate
                else: duplicates+=1
                gates=candidate
                smaller,why=compress(gates,base)
                if smaller is not None:
                    payload={'found':True,'reason':why,'seconds':time.monotonic()-start,
                             'attempts':attempts,'accepted':accepted,'seed':a.seed,
                             'gates':smaller,'gate_count':len(smaller),
                             'positive_basis':len(base.EDGES),'negative_basis':len(base.INDEPENDENT)}
                    a.out.write_text(json.dumps(payload)+'\n')
                    print(json.dumps({k:v for k,v in payload.items() if k!='gates'}),flush=True)
                    return
        now=time.monotonic()
        if now>=next_restart:
            if rng.randrange(2): gates=base.distributed_star(rng,rng.randrange(2)==0)
            else: gates=rng.choice(bank)
            assert valid(gates,base)
            next_restart=now+120
        if now>=next_report:
            payload={'progress':True,'seconds':now-start,'attempts':attempts,'accepted':accepted,
                     'distinct':changed,'duplicates':duplicates,'by_kind':kinds}
            print(json.dumps(payload),flush=True)
            a.out.write_text(json.dumps(dict(payload,seed=a.seed,gates=gates,gate_count=65))+'\n')
            next_report=now+30
    payload={'finished':True,'seconds':time.monotonic()-start,'attempts':attempts,
             'accepted':accepted,'distinct':changed,'duplicates':duplicates,'by_kind':kinds,
             'seed':a.seed,'gate_count':65,'found':False}
    a.out.write_text(json.dumps(dict(payload,gates=gates))+'\n')
    print(json.dumps(payload),flush=True)

if __name__=='__main__': main()
