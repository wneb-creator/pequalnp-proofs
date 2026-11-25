import argparse,json,time
from pathlib import Path
from synth_circuit import check

def prune(gates):
    needed={9+len(gates)}
    for j in range(len(gates)-1,-1,-1):
        if 10+j in needed:needed.update(gates[j][1:])
    renamed={i:i for i in range(10)};out=[]
    for j,(op,a,b) in enumerate(gates):
        if 10+j in needed:
            renamed[10+j]=10+len(out);out.append((op,renamed[a],renamed[b]))
    return out

def optimize(gates):
    n=len(gates);best=n+11;best_phase=0;start=time.monotonic()
    for phases in range(1<<n):
        bad=0
        for j,(op,a,b) in enumerate(gates):
            out=(phases>>j)&1
            for source,sign in [(a,out^(op==3)),(b,out^(op==2))]:
                stored=((phases>>(source-10))&1) if source>=10 else 0
                if sign!=stored:bad|=1<<source
            if bad.bit_count()>=best:break
        else:
            if (phases>>(n-1))&1:bad|=1<<(n+9)
            cost=bad.bit_count()
            if cost<best:
                best=cost;best_phase=phases
                print(json.dumps({'best_NOT_count':best,'phase_mask':phases,'seconds':time.monotonic()-start}),flush=True)
                if best==0:break
    actual=[];wire={i:i for i in range(10)};complement={}
    def source(i,required):
        stored=((best_phase>>(i-10))&1) if i>=10 else 0
        if stored==required:return wire[i]
        if i not in complement:
            complement[i]=10+len(actual);actual.append((2,wire[i],0))
        return complement[i]
    for j,(op,a,b) in enumerate(gates):
        out=(best_phase>>j)&1
        left=source(a,out^(op==3));right=source(b,out^(op==2))
        physical_op=(1 if op==1 else 0)^out
        wire[10+j]=10+len(actual);actual.append((physical_op,left,right))
    output=source(9+n,0)
    assert output==9+len(actual)
    assert len(actual)==n+best
    return actual,best,best_phase

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('output');args=p.parse_args()
    d=json.loads(Path(args.input).read_text());g=d['gates']
    if g and isinstance(g[0][0],str):g=[({'and':0,'or':1}[o],a,b) for o,a,b in g]
    assert not check(g,signed=True),'The signed circuit does not compute the Petersen function.'
    g=prune(g)
    actual,cost,phases=optimize(g)
    assert not check(actual),'The physical circuit failed exhaustive verification.'
    Path(args.output).write_text(json.dumps({'gates':actual,'size':len(actual),'NOT_count':cost,'phase_mask':phases,'output':9+len(actual)},indent=2))
    print('Verified physical circuit:',len(actual),'gates;',cost,'NOT gates.',flush=True)
