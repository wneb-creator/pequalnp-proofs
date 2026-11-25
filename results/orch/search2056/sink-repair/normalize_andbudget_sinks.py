import argparse,copy,datetime,hashlib,importlib.util,json
from pathlib import Path

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def sink_refs(model):
    selected=set(model['output'])
    return sum(i>=26 and i-26 in selected for rec in model['ands'] for key in ('left','right') for i in rec[key])

def make_sinks(module,normalizer,model,K):
    edges,rows=module.geometry();_,before=module.evaluate(model,rows);out=copy.deepcopy(model)
    for j in list(out['output']):
        for k in range(j+1,len(out['ands'])):
            for key in ('left','right'):out['ands'][k][key]=[i for i in out['ands'][k][key] if i!=26+j]
    false_records=set()
    for j,rec in enumerate(out['ands']):
        for key in ('left','right'):rec[key]=[i for i in rec[key] if i<26 or i-26 not in false_records]
        if not rec['left'] or not rec['right']:
            rec['left']=[];rec['right']=[];false_records.add(j)
    out['output']=[j for j in out['output'] if j not in false_records]
    _,after=module.evaluate(out,rows);assert before==after
    assert normalizer.cost(out)[0]<=normalizer.cost(model)[0]
    assert sink_refs(out)==0
    normalized,record=normalizer.normalize(module,out,K)
    assert sink_refs(normalized)==0 and normalizer.cost(normalized)[0]<=normalizer.cost(model)[0]
    _,final=module.evaluate(normalized,rows);P=(1<<52)-1
    positions={r:k for k,r in enumerate(rows)};permutation=record['permutation']
    for k,row in enumerate(rows):
        acted=sum(1<<permutation[i] for i in range(26) if row>>i&1)
        old=bool(before>>k&1);now=bool(final>>positions[acted]&1)
        assert (old==now) if k<52 else (not now or old)
    missing=[k for k in range(52) if not(final>>k&1)]
    record.update({'before_sink_cost_active_memberships':normalizer.cost(model),
                   'after_sink_cost_active_memberships':normalizer.cost(out),
                   'after_all_cost_active_memberships':normalizer.cost(normalized),
                   'deleted_output_reference_occurrences':sink_refs(model),
                   'selected_output_records_are_sinks':True,
                   'exact_sink_output_preserved_on756rows':True,
                   'missing_edge_indices':missing,
                   'repair_by_atomic_edges_cost_bound':normalizer.cost(normalized)[0]+2*len(missing)})
    return normalized,record

def main():
    p=argparse.ArgumentParser();p.add_argument('--encoder',required=True);p.add_argument('--normalizer',required=True);p.add_argument('--input',required=True);p.add_argument('--output',required=True);p.add_argument('--report',required=True);p.add_argument('--ands',type=int,default=16);a=p.parse_args()
    module=load(a.encoder,'encoder');normalizer=load(a.normalizer,'normalizer');raw=Path(a.input).read_bytes();model=json.loads(raw);out,report=make_sinks(module,normalizer,model,a.ands)
    path=Path(a.output);path.write_text(json.dumps(out,indent=2)+'\n');report.update({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'input_sha256':hashlib.sha256(raw).hexdigest(),'output_sha256':hashlib.sha256(path.read_bytes()).hexdigest()});Path(a.report).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
