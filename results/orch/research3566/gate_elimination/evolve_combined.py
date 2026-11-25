import importlib.util
from pathlib import Path

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('evolve_amplification',HERE/'evolve_amplification.py')
ea=importlib.util.module_from_spec(spec);spec.loader.exec_module(ea)
spec=importlib.util.spec_from_file_location('pendant_helpers',HERE/'pendant_helpers.py')
ph=importlib.util.module_from_spec(spec);spec.loader.exec_module(ph)
from functools import lru_cache
from itertools import combinations

N=ea.N;rh=ea.rh;COUNTS=ea.COUNTS
COUNTS.update(pendant_eligible_cases=0,pendant_positive_rise_cases=0,pendant_subsets=0,combined_improvement_cases=0)

@lru_cache(maxsize=65536)
def rise_upper(key,mask):
    centers=tuple(v for v in range(N) if (mask>>v)&1)
    return ph.augmented_cover(N,ea.graph_info(key)[4],centers)-ea.graph_info(key)[2]

def pendant_eligibility(values,records,output,F):
    todo=[output];seen=set();eligible={}
    while todo:
        w=todo.pop()
        if w<N or w in seen:continue
        seen.add(w);op,u,v=records[w]
        if op==1:todo.extend((u,v));continue
        for operand,f in enumerate((u,v)):
            if f<N:center=f
            else:
                support=[i for i in range(N) if (values[f]>>(1<<i))&1]
                if len(support)!=1:continue
                center=support[0]
                if values[f]&~(ea.INPUT[center]|F):continue
                assert not(ea.INPUT[center]&~values[f])
            eligible.setdefault(center,[]).append((w-N,operand))
    return eligible

@lru_cache(maxsize=32768)
def best_pendant(key,signature):
    eligible=dict(signature);mask=sum(1<<v for v in eligible)
    upper=rise_upper(key,mask)
    if upper==0:return 0,(),0,0
    best=0;choices=();checked=0
    for k in range(min(4,len(eligible)),0,-1):
        for centers in combinations(sorted(eligible),k):
            assignment=ph.assignment(centers,eligible)
            if assignment is None:continue
            checked+=1;rise=rise_upper(key,sum(1<<v for v in centers))
            if rise>best:best=rise;choices=tuple(assignment)
            if best>=upper:return best,choices,checked,upper
    return best,choices,checked,upper

def apply_pendant(g,key,choices):
    values,aliases,records,cones=rh.normalize(N,g,N+len(g)-1)
    mapping={i:i for i in range(N)};full=[];full_index={}
    for w in sorted(records):
        op,u,v=records[w];full_index[w]=len(full)
        full.append((op,mapping[u],mapping[v]));mapping[w]=N+len(full)-1
    translated=[(v,full_index[N+j],operand) for v,j,operand in choices]
    return ph.extend(N,ea.graph_info(key)[4],full,mapping[aliases[-1]],translated)

def evaluate(g,min_edges=14,force_audit=False):
    COUNTS['evaluated']+=1
    values,aliases,records,cones=rh.normalize(N,g,N+len(g)-1)
    out=values[-1];output_cone=cones[aliases[-1]];cost=output_cone.bit_count()
    bad=sum((out>>p)&1 for p in ea.BAD)+2*sum((out>>p)&1 for p in ea.SING)
    key=sum(((out>>p)&1)<<i for i,(_,_,p,_) in enumerate(ea.PAIR))
    F,m,tau,c4,edges=ea.graph_info(key);extra=(out&~F).bit_count();assert not(F&~out)
    gain=m+tau-1-cost;amplification=gain;helperprofit=gain;audit=None;helpers=[];upper=gain
    rise=0;choices=();eligible={};pendantupper=0
    valid=extra==bad==c4==0 and m>0
    if valid:
        COUNTS['valid']+=1
        helpers,improvement=ea.cheap_helpers(key,F,values,records,cones,output_cone);upper+=improvement
        if helpers:COUNTS['safe_helper_cases']+=1
        if improvement>0 or gain>0 or force_audit:
            COUNTS['full_audits']+=1
            audit=rh.audit_case(N,edges,g,N+len(g)-1,subset_budget_s=0.05,build_extension=True)
            helperprofit=audit['best_extension_profit']
            if not audit['subset_complete'] and not audit.get('witness'):COUNTS['incomplete_audits']+=1
            assert helperprofit<=upper
        eligible=pendant_eligibility(values,records,aliases[-1],F)
        if eligible:
            COUNTS['pendant_eligible_cases']+=1
            signature=tuple((v,tuple(sorted(opts))) for v,opts in sorted(eligible.items()))
            rise,choices,checked,pendantupper=best_pendant(key,signature)
            COUNTS['pendant_subsets']+=checked
            if rise:COUNTS['pendant_positive_rise_cases']+=1
        amplification=helperprofit+rise;upper+=pendantupper
        if amplification>gain:COUNTS['combined_improvement_cases']+=1
        if amplification>0 and rise:
            ext=apply_pendant(g,key,choices)
            combined=rh.audit_case(ext['n'],ext['edges'],ext['gates'],ext['output'],subset_budget_s=5,build_extension=True)
            assert combined['best_extension_profit']>=amplification
            assert combined.get('witness')
            audit={'helper_audit':audit,'pendant_intermediate':ext,**combined}
            amplification=combined['best_extension_profit']
    signature=(tuple(sorted((h[1],(h[2]&~output_cone).bit_count()) for h in helpers)),tuple(sorted(eligible)))
    metrics={'base_gain':gain,'amplification_profit':amplification,'helper_profit':helperprofit,'pendant_rise':rise,'pendant_upper':pendantupper,
      'pendant_choices':choices,'eligible_centers':len(eligible),'optimistic_profit':upper,
      'extra_rows':extra,'bad_pairs':bad,'four_cycles':c4,'edges':m,'cover':tau,'cost':cost,
      'safe_helpers':len(helpers),'helper_signatures':signature,'valid':valid,'graph_key':key}
    score=8*amplification+0.2*m-(12*bad+24*c4+2*ea.math.log2(1+extra))
    if m<min_edges:score=-1000000
    return score,metrics,audit

original_load_seeds=ea.load_seeds

def load_seeds():
    seeds=original_load_seeds();seen=set(seeds)
    rows=ea.json.loads((HERE/'pendant-audit-results.json').read_text())['cases']
    rows=[r for r in rows if r.get('max_cover_rise',0)>0]
    one=sorted((r for r in rows if r['max_cover_rise']==1),key=lambda r:(r['best_profit'],r['generalized_choices'],-r['raw_gates']),reverse=True)[:4]
    two=sorted((r for r in rows if r['max_cover_rise']>=2),key=lambda r:(r['best_profit'],r['generalized_choices'],-r['raw_gates']),reverse=True)[:4]
    wanted={r['source'] for r in one+two}
    for source,n,edges,gates,output in ph.saved_cases():
        if source not in wanted:continue
        assert n==8 and output==n+len(gates)-1
        pm=[0,1,2,3,7,8,9,10]
        def wire(w):return pm[w] if w<n else w-n+N
        g=tuple((0 if op in (0,'and') else 1,wire(u),wire(v)) for op,u,v in gates)
        if g not in seen:seen.add(g);seeds.append(g)
        wanted.remove(source)
    assert not wanted
    return seeds

ea.load_seeds=load_seeds

def validate():
    checks=[]
    for i,g in enumerate(ea.load_seeds()):
        _,m,_=evaluate(g,min_edges=8)
        direct=rh.audit_case(N,ea.graph_info(m['graph_key'])[4],g,N+len(g)-1)
        pendant=ph.audit_case(N,ea.graph_info(m['graph_key'])[4],g,N+len(g)-1)
        assert direct['subset_complete']
        assert direct['best_extension_profit']==m['helper_profit']
        assert pendant['max_cover_rise']==m['pendant_rise']
        assert direct['best_extension_profit']+pendant['max_cover_rise']==m['amplification_profit']
        if m['pendant_rise']:
            ext=apply_pendant(g,m['graph_key'],m['pendant_choices'])
            combined=rh.audit_case(ext['n'],ext['edges'],ext['gates'],ext['output'])
            assert combined['best_extension_profit']>=m['amplification_profit']
        checks.append({'seed':i,**ea.log_metrics(m)})
    result={'checks':checks,'counters':COUNTS}
    (HERE/'evolution-combined-validation.json').write_text(ea.json.dumps(result,indent=2)+'\n')
    print(ea.json.dumps(result),flush=True)

ea.evaluate=evaluate
if __name__=='__main__':
    import sys
    if '--validate-combined' in sys.argv:validate()
    else:ea.main()
