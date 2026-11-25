import argparse,copy,datetime,hashlib,importlib.util,json
from pathlib import Path

def cost(model):
    active=sum(bool(r['left']) for r in model['ands'])
    memberships=sum(len(r['left'])+len(r['right']) for r in model['ands'])+len(model['output'])
    return memberships-active-1,active,memberships

def normalize(module,model,K):
    edges,rows=module.geometry();P=(1<<52)-1;mask=(1<<len(rows))-1;N=mask^P
    assert len(model['ands'])<=K
    assert all(bool(r['left'])==bool(r['right']) for r in model['ands'])
    oldvals,oldout=module.evaluate(model,rows);assert oldout&P
    normal=copy.deepcopy(model)
    cleared=atomic=0
    for j,rec in enumerate(normal['ands']):
        profile=oldvals[26+j]&P
        if not profile:
            cleared+=int(bool(rec['left']));normal['ands'][j]={'left':[],'right':[]}
        elif profile.bit_count()==1:
            p,l=edges[profile.bit_length()-1];normal['ands'][j]={'left':[p],'right':[l]};atomic+=1
    vals,value=module.evaluate(normal,rows)
    assert all((x&P)==(y&P) and not(y&N&~x) for x,y in zip(oldvals,vals))
    assert cost(normal)[0]<=cost(model)[0]
    active=[j for j,r in enumerate(normal['ands']) if r['left']]
    renaming={old:new for new,old in enumerate(active)}
    compact={'ands':[],'output':[renaming[j] for j in normal['output'] if j in renaming]}
    for j in active:
        record={}
        for side in ('left','right'):
            record[side]=sorted(i if i<26 else 26+renaming[i-26]
                                for i in normal['ands'][j][side] if i<26 or i-26 in renaming)
            assert record[side] and all(i<26+len(compact['ands']) for i in record[side])
        compact['ands'].append(record)
    assert compact['output'] and cost(compact)[0]<=cost(normal)[0]
    _,compacted_value=module.evaluate(compact,rows);assert compacted_value==value
    v=compact['ands'][0]['left'][0];assert 0<=v<26
    dual=v>=13;shift=v%13
    def perm(i):
        assert 0<=i<26
        if dual:i=i+13 if i<13 else i-13
        return (i-shift)%13 if i<13 else 13+(i-13+shift)%13
    permutation=[perm(i) for i in range(26)]
    assert permutation[v]==0 and sorted(permutation)==list(range(26))
    E={tuple(e) for e in edges};assert {tuple(sorted((perm(p),perm(l)))) for p,l in E}==E
    transformed=copy.deepcopy(compact)
    for rec in transformed['ands']:
        for side in ('left','right'):rec[side]=sorted(perm(i) if i<26 else i for i in rec[side])
    vals,newout=module.evaluate(transformed,rows)
    row_index={r:k for k,r in enumerate(rows)}
    for k,r in enumerate(rows):
        acted=sum(1<<perm(i) for i in range(26) if r>>i&1)
        assert acted in row_index
        assert bool(value>>k&1)==bool(newout>>row_index[acted]&1)
    for j,rec in enumerate(transformed['ands']):
        profile=vals[26+j]&P
        if profile.bit_count()==1:
            p,l=edges[profile.bit_length()-1];rec['left']=[p];rec['right']=[l]
    _,oriented=module.evaluate(transformed,rows);assert oriented==newout
    assert 0 in transformed['ands'][0]['left']
    transformed['ands'].extend({'left':[],'right':[]} for _ in range(K-len(transformed['ands'])))
    _,final_value=module.evaluate(transformed,rows);assert final_value==newout
    assert cost(transformed)[0]<=cost(model)[0]
    ordinary=module.materialize(transformed);assert module.ordinary_eval(ordinary,rows)==newout
    A=cost(transformed)[1]
    assert all(bool(rec['left'])==(j<A) for j,rec in enumerate(transformed['ands']))
    assert all(j<A for j in transformed['output'])
    report={'before_cost_active_memberships':cost(model),'after_cost_active_memberships':cost(transformed),
            'zero_profile_clearings':cleared,'singleton_orientations':atomic,'chosen_first_left':v,
            'duality_used':dual,'translation':shift,'permutation':permutation,
            'first_record':transformed['ands'][0],'positive_rows':52,'negative_rows':704,
            'before_missed':52-(oldout&P).bit_count(),'after_missed':52-(newout&P).bit_count(),
            'before_false_positives':(oldout&N).bit_count(),'after_false_positives':(newout&N).bit_count(),
            'ordinary_size':ordinary['size'],'normalization_and_relabeling_checked':True}
    return transformed,report

def main():
    p=argparse.ArgumentParser();p.add_argument('--encoder',required=True);p.add_argument('--input',required=True);p.add_argument('--output',required=True);p.add_argument('--report',required=True);p.add_argument('--ands',type=int,default=16);a=p.parse_args()
    spec=importlib.util.spec_from_file_location('and_budget',a.encoder);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    original=Path(a.input).read_bytes();model=json.loads(original);new,report=normalize(m,model,a.ands)
    output=Path(a.output);output.write_text(json.dumps(new,indent=2)+'\n')
    report.update({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'input_sha256':hashlib.sha256(original).hexdigest(),'output_sha256':hashlib.sha256(output.read_bytes()).hexdigest(),'encoder_sha256':hashlib.sha256(Path(a.encoder).read_bytes()).hexdigest()})
    Path(a.report).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
