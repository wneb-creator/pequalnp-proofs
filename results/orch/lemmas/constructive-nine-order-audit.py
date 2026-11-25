from pathlib import Path
import sys,json,hashlib,datetime

base=Path(sys.argv[1])
full=(1<<16384)-1
inputs=[sum(1<<mask for mask in range(16384) if mask&(1<<i)) for i in range(14)]
reports=[]
for tag in ['sat-p14-compact-nine35-control','sat-p14-compact-nine-host-control']:
    metadata=json.loads((base/(tag+'.metadata.json')).read_text())
    control=json.loads((base/(tag+'.compact-control.json')).read_text())
    assignment={int(k):bool(v) for k,v in json.loads((base/(tag+'.complete-assignment.json')).read_text()).items()}
    assert set(assignment)==set(range(1,metadata['variables']+1))
    count=0
    with (base/(tag+'.cnf')).open() as source:
        assert source.readline().split()==['p','cnf',str(metadata['variables']),str(metadata['clauses'])]
        for line in source:
            values=list(map(int,line.split()));assert values[-1]==0
            assert any(assignment[abs(v)]==(v>0) for v in values[:-1]),(tag,count)
            count+=1
    assert count==metadata['clauses']
    atoms=[]
    for j,atom in enumerate(control['atoms']):
        slots=[]
        for slot in atom['slots']:
            assert all(0<=i<14 for i in slot['primary']) and all(0<=i<j for i in slot['prior'])
            value=0
            for i in slot['primary']:value|=inputs[i]
            for i in slot['prior']:value|=atoms[i]
            slots.append(value)
        atoms.append(slots[0]&slots[1])
    result=0
    for j in control['final']:result|=atoms[j]
    target=0
    for p,l in metadata['edges']:target|=inputs[p]&inputs[l]
    assert result==target
    derivatives=[]
    for base_input,seed in [(0,7),(7,0)]:
        values=[];ds=[]
        for atom in control['atoms']:
            sv=[];sd=[]
            for slot in atom['slots']:
                sv.append(base_input in slot['primary'] or any(values[k] for k in slot['prior']))
                sd.append(seed in slot['primary'] or any(ds[k] for k in slot['prior']))
            values.append(sv[0] and sv[1]);ds.append((sv[0] and sd[1]) or (sd[0] and sv[1]))
        out=any(ds[j] for j in control['final']);assert not out;derivatives.append(out)
    maxima=[max([k for slot in atom['slots'] for k in slot['prior']],default=-1) for atom in control['atoms']]
    assert maxima==sorted(maxima)
    for j,flags in enumerate(metadata['enhancements']['ordering']):
        for k,flag in enumerate(flags):
            expected=j<len(maxima) and maxima[j]>=k
            assert assignment[flag]==expected
    reports.append({'tag':tag,'clauses_checked':count,'variables_checked':len(assignment),'truth_rows_checked':16384,'direct_raw_derivatives':derivatives,'active_atoms':len(atoms)})
report={'verdict':'PASS','reviewer':'constructive_search','reviewed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'extension_sha256':hashlib.sha256((base/'sat-p14-compact-nine.py').read_bytes()).hexdigest(),'core_sha256':hashlib.sha256((base/'sat-p14-compact.py').read_bytes()).hexdigest(),'controls':reports,'mathematical_audit':['Greedy ready-AND scheduling by least maximum mapped predecessor gives nondecreasing maxima: old ready keys are no smaller; newly ready nodes depend on the just-emitted atom and therefore have a strictly larger key.','The code canonicalizer implements that rule, remaps every dependency and final reference, preserves primary host labels, then reorients operands.','Each ordering threshold is exactly the OR of both operand prior selectors at indices at least k; old-threshold implies next-threshold only when next atom is active, so inactive suffixes are allowed.','Both complete positive controls pass all clauses, all16384truth rows, direct raw derivative checks, nondecreasing maxima and every threshold auxiliary variable.','Nine-free cooccurrence cuts are outside this review; status_review owns their justification.'],'scope':'Encoding and positive-control review only; no SAT result or Lean certificate claimed.'}
(base/'constructive-nine-order-review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'verdict':'PASS','extension_sha256':report['extension_sha256'],'controls':reports}))
