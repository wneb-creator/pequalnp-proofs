import json
from pathlib import Path
from core_tap_cost import compact
from core_tap_synthesis import validate

BASE=Path('results/orch/lemmas/lean_baseline/sat')
SOURCE=Path('results/orch/lemmas/reduction_analysis/full_residual_algebraic_5extra_joint60_seed.json')

def main():
    source=json.loads(SOURCE.read_text())
    pack=json.loads((BASE/'full_residual_tap.json').read_text())
    case=pack['cases'][0];n=case['inputs'];tests=case['constraints']
    inputs=[sum(1<<k for k,t in enumerate(tests) if t['input']>>i&1) for i in range(n)]
    positive=sum(1<<k for k,t in enumerate(tests) if t['residual'])
    negative=sum(1<<k for k,t in enumerate(tests) if not t['residual'])
    tap_care=sum(1<<k for k,t in enumerate(tests) if t['tap'] is not None)
    tap_true=sum(1<<k for k,t in enumerate(tests) if t['tap'] is True)
    def evaluate(gates,outputs):
        values=inputs.copy()
        for op,a,b in gates: values.append(values[a]|values[b] if op else values[a]&values[b])
        h,t=(values[o] for o in outputs)
        if h&positive!=positive or (t^tap_true)&tap_care: return None
        return (h&negative).bit_count()
    small_masks=[0]+[1<<v for v in range(n)]+[(1<<a)|(1<<b) for a in range(n) for b in range(a+1,n)]
    small_masks=[m for m in small_masks if not any(m>>a&1 and m>>b&1 for a,b in pack['edges'])]
    small_inputs=[sum(1<<k for k,m in enumerate(small_masks) if m>>v&1) for v in range(n)]
    small_q=0
    for v in case['tap_input_indices']: small_q|=small_inputs[v]
    def dirty_witness(gates,outputs):
        values=small_inputs.copy();dirty=0
        for op,a,b in gates:
            values.append(values[a]|values[b] if op else values[a]&values[b])
            if not op and a!=b: dirty|=values[-1]
        eligible=dirty&~values[outputs[0]]&~(values[outputs[1]]^small_q)&((1<<len(small_masks))-1)
        return small_masks[(eligible&-eligible).bit_length()-1] if eligible else None
    original=evaluate(source['gates'],source['outputs']);best=original;total=0;valid=0
    improvements=[];qualified_best=original
    for gate_index,(op,a,b) in enumerate(source['gates']):
        for side,wire in enumerate((a,b)):
            for other in range(n+gate_index):
                if wire==other: continue
                mapped={i:i for i in range(n)};new=[]
                for i,(kind,left,right) in enumerate(source['gates']):
                    parents=[mapped[left],mapped[right]]
                    if i==gate_index:
                        new.append([0,*sorted((mapped[wire],mapped[other]))])
                        parents[side]=n+len(new)-1
                    mapped[n+i]=n+len(new)
                    new.append([kind,*sorted(parents)])
                outputs=[mapped[o] for o in source['outputs']]
                total+=1;score=evaluate(new,outputs)
                if score is None: continue
                valid+=1
                if score<original:
                    witness=dirty_witness(new,outputs)
                    improvements.append({'gate':gate_index,'side':side,'other':other,'errors':score,'dirty_witness':witness})
                    if witness is not None and score<qualified_best:
                        qualified_best=score
                        (BASE/'filter_edge_qualified_best.json').write_text(json.dumps({'gates':new,'outputs':outputs,'dirty_witness':witness,'residual_errors':score,'target_met':False}))
                if score<best:
                    new,outputs=compact(new,outputs,n)
                    best=score
                    result={'gates':new,'outputs':outputs,'residual_errors':score,
                            'tap_is_correct':True,'target_met':score==0 and len(new)<=61,
                            'source_gate':gate_index,'source_side':side,'filter_other':other}
                    (BASE/'filter_edge_best.json').write_text(json.dumps(result))
                    print('IMPROVED',total,'errors',score,'gates',len(new),flush=True)
                    if score==0:
                        assert validate(pack,case,new,outputs)
                        (BASE/'EXACT-RESIDUAL-TAP.json').write_text(json.dumps(result))
                        return
    (BASE/'filter_edge_improvements.json').write_text(json.dumps(improvements))
    print('IMPROVING',len(improvements),'DIRTY-QUALIFIED',sum(x['dirty_witness'] is not None for x in improvements),'QUALIFIED-BEST',qualified_best)
    print('COMPLETE candidates',total,'preservepositives/tap',valid,'baselineerrors',original,'besterrors',best)

if __name__=='__main__':main()
