"""Finite constant propagation for gates false on every minimal positive input."""
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
ALG = HERE.parent/'algebra_strategy'
helpers = runpy.run_path(str(ALG/'assemble_five_owner.py'))
compact, assemble = helpers['compact_core'], helpers['assemble_five']
summaries=[]
for tag,pool_name in [('five','joint5suppressed-pool.json'),('global','global13suppressed-pool.json')]:
    pool=json.loads((HERE/pool_name).read_text())
    (HERE/(tag+'-positive-prune-source-pool.json')).write_text(json.dumps(pool))
    if tag=='five':
        case=json.loads((ALG/'five-owner-joint-packet.json').read_text())[0]
        n=case['inputs'];tests=case['tests']
    else:
        case=None;n=26;tests=json.loads((HERE/'full-case.json').read_text())['tests']
    columns=[sum((mask>>i&1)<<j for j,(mask,_) in enumerate(tests)) for i in range(n)]
    target=sum(label<<j for j,(_,label) in enumerate(tests))
    improvements=[];inactive_models=0
    for index,item in enumerate(pool):
        old,old_output,_=compact(n,item['gates'])
        assert old_output==n+len(old)-1
        values=columns.copy()
        for op,a,b in old:values.append(values[a]|values[b] if op else values[a]&values[b])
        old_error=(values[-1]&~target).bit_count()
        inactive=[i for i in range(len(old)) if values[n+i]&target==0]
        if not inactive:continue
        inactive_models+=1
        ren=list(range(n));made=[];cache={}
        for i,(op,a,b) in enumerate(old):
            if values[n+i]&target==0:ren.append(-1);continue
            a,b=ren[a],ren[b]
            if a<0 or b<0:
                assert op==1
                ren.append(max(a,b));continue
            if a==b:ren.append(a);continue
            a,b=sorted((a,b));key=(op,a,b)
            if key not in cache:cache[key]=n+len(made);made.append([op,a,b])
            ren.append(cache[key])
        assert ren[-1]>=0
        gates,output,_=compact(n,made,ren[-1])
        assert output==n+len(gates)-1
        new=columns.copy()
        for op,a,b in gates:new.append(new[a]|new[b] if op else new[a]&new[b])
        assert new[-1]&target==target and new[-1]&~values[-1]==0
        error=(new[-1]&~target).bit_count()
        if tag=='five':
            _,before=assemble(case,old);_,after=assemble(case,gates)
            old_cost=before['core_gates']+before['prefix_extra_cost']
            cost=after['core_gates']+after['prefix_extra_cost'];assert after['within_budget']
        else:old_cost=len(old);cost=len(gates)
        assert cost<=old_cost
        if error<old_error or cost<old_cost:
            improvements.append(dict(pool_index=index,gates=gates,old_errors=old_error,new_errors=error,
                                     old_effective_cost=old_cost,new_effective_cost=cost,
                                     and_count=sum(op==0 for op,_,_ in gates),inactive_gates_removed=inactive))
    (HERE/(tag+'-positive-prune-results.json')).write_text(json.dumps(improvements))
    summary=dict(case=tag,models=len(pool),positive_inactive_models=inactive_models,
                 improved=len(improvements),best_errors=min((x['new_errors'] for x in improvements),default=None))
    summaries.append(summary)
(HERE/'positive-prune-summary.json').write_text(json.dumps(summaries,indent=2));print(summaries)
