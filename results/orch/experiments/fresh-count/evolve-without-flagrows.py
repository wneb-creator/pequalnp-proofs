import json
import math
from pathlib import Path
import random
import sys
import time

root=Path('/tmp/oec/pequalnp-pilot-73/counterexample')
out=Path('/tmp/oec/pequalnp-pilot-73/fresh-count/without-flagrows');out.mkdir(exist_ok=True)
seed=208977
rng=random.Random(seed)
duration=int(sys.argv[1]) if len(sys.argv)>1 else 1200
d=json.loads((root/'promises.json').read_text())
d['negative']=[r for r in d['negative'] if not ((r&8191).bit_count()==3 and (r>>13).bit_count()==3)]
rows=d['positive']+d['negative'];np=len(d['positive'])
positive=(1<<np)-1;mask=(1<<len(rows))-1;negative=mask^positive
raw=[sum(1<<j for j,r in enumerate(rows) if r>>i&1) for i in range(26)]

def evaluate(gs):
    vs=raw.copy()
    for op,a,b in gs:vs.append((vs[a]|vs[b]) if op else (vs[a]&vs[b]))
    return (positive&~vs[-1]).bit_count(),(negative&vs[-1]).bit_count(),vs

def balanced_or(g,terms):
    terms=terms.copy()
    while len(terms)>1:
        a=terms.pop(rng.randrange(len(terms)));b=terms.pop(rng.randrange(len(terms)))
        g.append((1,a,b));terms.append(25+len(g))
    return terms[0]

def gate(g,op,a,b):
    g.append((op,a,b));return 25+len(g)

def standard(kind):
    g=[]
    dual=bool(rng.randrange(2))
    def pv(p):return 13+p if dual else p
    def lv(l):return l if dual else 13+l
    adj=d['N'] if dual else d['lines_through']
    pivot=rng.randrange(13)
    if kind==3:
        # Overapproximations approach the target from the opposite side.
        strategy=rng.randrange(3)
        chosen=rng.sample(range(13),6 if strategy==0 else 3 if strategy==1 else 4)
        if strategy in (1,2):
            import itertools
            while any(all(adj[p]>>l&1 for p in triple) for triple in itertools.combinations(chosen,3) for l in range(13)):
                chosen=rng.sample(range(13),3 if strategy==1 else 4)
        groups=[chosen[i:i+2] for i in range(0,6,2)] if strategy==0 else [chosen]
        groups += [[p] for p in range(13) if p not in chosen]
        rng.shuffle(groups);terms=[]
        for group in groups:
            pm=balanced_or(g,[pv(p) for p in group]);neighbors=0
            for p in group:neighbors|=adj[p]
            lm=balanced_or(g,[lv(l) for l in range(13) if neighbors>>l&1])
            terms.append(gate(g,0,pm,lm))
        h=balanced_or(g,terms)
        assert len(g)<=61
        while len(g)<61:
            bound=26+len(g);gate(g,rng.randrange(2),rng.randrange(bound),rng.randrange(bound))
        copy=gate(g,1,h,h);gate(g,0,h,copy)
    elif kind==0:
        # One star is distributed through the final OR, making an AND root.
        order=[p for p in range(13) if p!=pivot];rng.shuffle(order)
        terms=[]
        for p in order:
            ns=[lv(l) for l in range(13) if adj[p]>>l&1]
            q=balanced_or(g,ns);terms.append(gate(g,0,pv(p),q))
        rest=balanced_or(g,terms)
        q=balanced_or(g,[lv(l) for l in range(13) if adj[pivot]>>l&1])
        a=gate(g,1,rest,pv(pivot));b=gate(g,1,rest,q);gate(g,0,a,b)
    elif kind==1:
        # An incident point/line pair gives a genuinely mixed 67-gate seed.
        line=rng.choice([l for l in range(13) if adj[pivot]>>l&1])
        terms=[];order=[p for p in range(13) if p!=pivot];rng.shuffle(order)
        for p in order:
            ns=[lv(l) for l in range(13) if l!=line and adj[p]>>l&1]
            q=balanced_or(g,ns);terms.append(gate(g,0,pv(p),q))
        rest=balanced_or(g,terms)
        r=balanced_or(g,[lv(l) for l in range(13) if l!=line and adj[pivot]>>l&1])
        s=balanced_or(g,[pv(p) for p in range(13) if p!=pivot and adj[p]>>line&1])
        ps=gate(g,0,pv(pivot),r);ls=gate(g,0,lv(line),s)
        a=balanced_or(g,[pv(pivot),rest,ls]);b=balanced_or(g,[lv(line),rest,ps]);gate(g,0,a,b)
    else:
        # A mixed point/line star cover; random orientation and one or two point stars.
        chosen=set(rng.sample(range(13),rng.choice([1,2])))
        terms=[]
        for p in chosen:
            q=balanced_or(g,[lv(l) for l in range(13) if adj[p]>>l&1])
            terms.append((pv(p),q))
        for l in rng.sample(range(13),13):
            ps=[pv(p) for p in range(13) if p not in chosen and adj[p]>>l&1]
            if ps:terms.append((lv(l),balanced_or(g,ps)))
        special=terms.pop(rng.randrange(len(terms)))
        term_wires=[gate(g,0,a,b) for a,b in terms]
        rest=balanced_or(g,term_wires)
        a=gate(g,1,rest,special[0]);b=gate(g,1,rest,special[1]);gate(g,0,a,b)
    assert evaluate(g)[0]==0 and (kind==3 or evaluate(g)[1]==0),(kind,len(g),evaluate(g)[:2])
    # Singer translations and multipliers, optionally followed by polarity.
    shift=rng.randrange(13);scale=rng.choice([1,3,9]);polarity=bool(rng.randrange(2))
    def auto(w):
        if w>=26:return w
        side=w//13;v=(scale*(w%13)+shift)%13
        if polarity:side=1-side;v=(-v)%13
        return 13*side+v
    g=[(op,auto(a),auto(b)) for op,a,b in g]
    assert evaluate(g)[0]==0 and (kind==3 or evaluate(g)[1]==0)
    return g

def remove(g,j,replacement):
    old=26+j
    def fix(x):return replacement if x==old else x-1 if x>old else x
    return [(op,fix(a),fix(b)) for i,(op,a,b) in enumerate(g) if i!=j]

def new_seed(kind):
    g=standard(kind)
    while len(g)>63:
        choices=[]
        for j,(op,a,b) in enumerate(g[:-1]):
            for repl in set([a,b]):
                trial=remove(g,j,repl);fn,fp,vs=evaluate(trial)
                choices.append((4*fn+fp,rng.random(),trial))
        choices.sort(key=lambda x:(x[0],x[1]))
        cutoff=choices[0][0]+rng.choice([0,0,2,4])
        pool=[x for x in choices[:16] if x[0]<=cutoff]
        g=rng.choice(pool)[2]
    fn,fp,vs=evaluate(g)
    return [g,fn,fp,vs,0]

def bit_choice(bits):
    k=rng.randrange(bits.bit_count())
    for _ in range(k):bits&=bits-1
    return (bits&-bits).bit_length()-1

def defect_path(gs,vs,bit,desired):
    j=len(gs)-1;path=[]
    while j>=0:
        path.append(j);op,a,b=gs[j]
        options=[w for w in (a,b) if ((vs[w]>>bit)&1)!=desired]
        if not options:break
        w=rng.choice(options)
        if w<26:break
        j=w-26
    return path

def desired_wire(vs,bound,bit,desired):
    for _ in range(12):
        a=rng.randrange(bound)
        if ((vs[a]>>bit)&1)==desired:return a
    return rng.randrange(bound)

def mutate(gs,vs):
    result=gs.copy();bad=(positive^vs[-1])&mask
    bit=bit_choice(bad);desired=int(bit<np)
    path=defect_path(gs,vs,bit,desired)
    mode=rng.randrange(100)
    count=1 if mode<78 else 2 if mode<94 else rng.choice([3,4])
    for _ in range(count):
        j=rng.choice(path) if rng.random()<0.65 else rng.randrange(63)
        op,a,b=result[j];bound=26+j
        if mode<12 and j!=62:
            op=1-op
        elif 12<=mode<22:
            # An associative rotation changes useful shared intermediates without changing this gate.
            opts=[]
            for child,other in [(a,b),(b,a)]:
                if child>=26 and child-26<j and other<child and result[child-26][0]==op:
                    opts.append((child,other))
            if opts:
                child,other=rng.choice(opts);cop,ca,cb=result[child-26]
                result[child-26]=(cop,ca,other);a,b=child,cb
            else:
                a=desired_wire(vs,bound,bit,desired)
        elif 22<=mode<34:
            # Change both pins at once to cross fitness barriers.
            a=desired_wire(vs,bound,bit,desired)
            b=desired_wire(vs,bound,bit,desired)
        else:
            replacement=desired_wire(vs,bound,bit,desired) if rng.random()<0.8 else rng.randrange(bound)
            if rng.randrange(2):a=replacement
            else:b=replacement
        result[j]=(0 if j==62 else op,a,b)
    op,a,b=result[-1]
    if a==b:b=(b+1)%(26+len(result)-1)
    result[-1]=(0,a,b)
    return result

def simplify(gs,vs):
    # Resubstitution is checked only on the reduced184-negative-row experiment domain.
    first={};redirect={}
    for i,v in enumerate(vs):
        if v in first:redirect[i]=first[v]
        else:first[v]=i
    if not redirect:return gs
    result=[(op,redirect.get(a,a),redirect.get(b,b)) for op,a,b in gs]
    if result[-1][1]==result[-1][2]:result[-1]=gs[-1]
    return result

def save_candidate(name,gs,fn,fp,iteration):
    assert len(gs)==63 and gs[-1][0]==0 and gs[-1][1]!=gs[-1][2]
    assert all(a<26+i and b<26+i for i,(_,a,b) in enumerate(gs))
    fn2,fp2,vs=evaluate(gs);assert (fn,fp)==(fn2,fp2)
    missing=[r for j,r in enumerate(d['positive']) if not (vs[-1]>>j&1)]
    falsepos=[r for j,r in enumerate(d['negative'],np) if vs[-1]>>j&1]
    record={'seed':seed,'iteration':iteration,'elapsed_s':time.monotonic()-start,'gates':gs,
            'false_negative_count':fn,'false_positive_count':fp,
            'missing_positive_masks':missing,'false_positive_masks':falsepos,
            'distinct_final_operands':gs[-1][1]!=gs[-1][2],
            'final_operand_constraint':'STRICT',
            'verdict':'VALID ONLY ON REDUCED TEST SET, NOT A GAP WITNESS' if fn==fp==0 else 'NOT A WITNESS'}
    (out/f'{name}.json').write_text(json.dumps(record,indent=2))

start=time.monotonic();iteration=0;last_report=start;last_seed=start
walkers=[];archive={};best_total=1000;best_pos=1000;best_zero_neg=1000
for folder in ['evolution','evolution-hot','evolution-singletons']:
    saved=json.loads((root/folder/'latest-population.json').read_text())
    for record in saved:
        g=[tuple(x) for x in record['gates']];fn,fp,vs=evaluate(g)
        op,a,b=g[-1]
        if a==b:
            alternatives=[i for i in range(88) if i!=a and vs[i]==vs[a]]
            if not alternatives:continue
            g[-1]=(0,a,alternatives[0])
        fn,fp,vs=evaluate(g);walkers.append([g,fn,fp,vs,0])
for i in range(max(0,24-len(walkers))):
    walkers.append(new_seed(i%4))
print('START seed',seed,'seconds',duration,'walkers',len(walkers),'initialization',time.monotonic()-start,flush=True)
(out/'configuration.json').write_text(json.dumps({'rng_seed':seed,'duration_s':duration,'walkers':len(walkers),
    'positive_rows':np,'negative_rows':len(d['negative']),'final_operand_constraint':'STRICT','initial_families':['distributed star65','mixed incident67','mixed starcover66+','merged hot overapproximation']}))
while time.monotonic()-start<duration:
    iteration+=1
    wi=iteration%len(walkers);g,fn,fp,vs,stale=walkers[wi]
    if fn==fp==0:
        save_candidate('WITNESS',g,fn,fp,iteration);print('FOUND',iteration,flush=True);break
    child=mutate(g,vs)
    if iteration%503==0:
        other=rng.choice(walkers)[0];lo=rng.randrange(63);hi=min(63,lo+rng.randrange(1,6))
        child[lo:hi]=other[lo:hi];child[-1]=(0,child[-1][1],child[-1][2])
    cn,cp,cv=evaluate(child)
    weight=[2,8,32,128][wi%4]
    old=weight*fn+fp;new=weight*cn+cp
    temperature=[0.05,0.15,0.4,0.8][wi%4]
    accept=new<=old or rng.random()<math.exp(min(0,(old-new)/temperature))
    if accept:
        if iteration%97==0:
            child=simplify(child,cv);cn,cp,cv=evaluate(child)
        walkers[wi]=[child,cn,cp,cv,0 if new<old else stale+1]
        fn,fp,g,vs=cn,cp,child,cv
        signature=vs[-1]
        if fn+fp<=8 and signature not in archive:
            archive[signature]=(g,fn,fp)
            if len(archive)>1000:archive.pop(next(iter(archive)))
    else:
        walkers[wi][4]+=1
    total=fn+fp
    changed=False
    if total<best_total:
        best_total=total;save_candidate('best-total',g,fn,fp,iteration);changed=True
    if fp==0 and fn<best_zero_neg:
        best_zero_neg=fn;save_candidate('best-zero-false-positive',g,fn,fp,iteration);changed=True
    if fn==0 and fp<best_pos:
        best_pos=fp;save_candidate('best-zero-false-negative',g,fn,fp,iteration);changed=True
    if changed:
        save_candidate(f'best-{iteration}',g,fn,fp,iteration)
        print('BEST',iteration,'fn',fn,'fp',fp,'seconds',round(time.monotonic()-start,2),flush=True)
    if fn==fp==0:
        save_candidate('WITNESS',g,fn,fp,iteration);print('FOUND',iteration,flush=True);break
    now=time.monotonic()
    if now-last_seed>25:
        wi=rng.randrange(len(walkers))
        if archive and rng.random()<0.5:
            eg,en,ep=rng.choice(list(archive.values()));_,_,ev=evaluate(eg)
            walkers[wi]=[eg.copy(),en,ep,ev,0]
        else:walkers[wi]=new_seed(wi%4)
        last_seed=now
    if now-last_report>30:
        print('PROGRESS seconds',round(now-start,1),'iterations',iteration,'archive',len(archive),
              'best_total',best_total,'best_clean_fn',best_zero_neg,'best_full_fp',best_pos,
              'walkers',[(w[1],w[2]) for w in walkers],flush=True)
        (out/'latest-population.json').write_text(json.dumps([{'gates':w[0],'fn':w[1],'fp':w[2]} for w in walkers]))
        last_report=now
else:
    print('DONE seconds',time.monotonic()-start,'iterations',iteration,'best_total',best_total,
          'best_clean_fn',best_zero_neg,'best_full_fp',best_pos,flush=True)
