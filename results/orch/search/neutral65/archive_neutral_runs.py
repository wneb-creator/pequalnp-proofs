import hashlib
import json
import shutil
from datetime import datetime, timezone
from pathlib import Path

scratch=Path('/tmp/oec/pequalnp-pilot-64')
archive=Path('results/orch/search/neutral65')
runs=[('neutral65-search-resumed.log','neutral65-best-resumed.json','neutral65_search.py',640165,1710),
      ('neutral65-search-v2-resumed.log','neutral65-best-v2-resumed.json','neutral65_search_v2.py',640166,1770),
      ('neutral66-search.log','neutral66-best.json','neutral66_search.py',640167,1200),
      ('neutral66-alternative-search.log','neutral66-alternative-best.json','neutral66_from_seed.py',640168,600)]
rows=[]
for log,result,program,seed,seconds in runs:
    d=json.loads((scratch/result).read_text())
    assert d.get('finished') is True, result+' is still running'
    assert d['seed']==seed
    assert d['seconds']>=seconds
    assert d.get('found') is False, result+' reports a possible witness; inspect separately'
    rows.append((log,result,program,seed,seconds,d))

def evaluate(gates,assignment,marked=None):
    values=[bool((assignment>>i)&1) for i in range(26)]
    derivatives=[i==marked for i in range(26)]
    for j,(op,a,b) in enumerate(gates):
        assert op in (0,1) and 0<=a<b<26+j
        if op==0:
            values.append(values[a] or values[b])
            derivatives.append(derivatives[a] or derivatives[b])
        else:
            values.append(values[a] and values[b])
            derivatives.append((values[a] and derivatives[b]) or (derivatives[a] and values[b]))
    return values[-1],derivatives[-1]

neighbors=[{l for l in range(13) if (p-l)%13 in (0,1,3,9)} for p in range(13)]
positives=[(1<<p)|(1<<(13+l)) for p in range(13) for l in neighbors[p]]
negatives=[]
for mask in range(1<<13):
    chosen={p for p in range(13) if (mask>>p)&1}
    lines={l for l in range(13) if all(l not in neighbors[p] for p in chosen)}
    points={p for p in range(13) if all(l not in neighbors[p] for l in lines)}
    if points==chosen:
        negatives.append(mask|sum(1<<(13+l) for l in lines))
assert len(positives)==52 and len(negatives)==704
validations=[]
for log,result,program,seed,seconds,d in rows:
    gates=d['gates']
    assert len(gates)==d['gate_count'] and len(gates) in (65,66)
    assert all(evaluate(gates,x)[0] for x in positives)
    assert all(not evaluate(gates,x)[0] for x in negatives)
    assert evaluate(gates,1,13)[1] is False
    assert evaluate(gates,1<<13,0)[1] is False
    validations.append({'result':result,'gates':len(gates),'AND':sum(g[0] for g in gates),
                        'positive_rows':52,'negative_rows':704,'both_derivatives_false':True,
                        'strictly_earlier_distinct_operands':True,'scalar_validation':'PASS'})
    for name in [log,result,program]:shutil.copyfile(scratch/name,archive/name)

meta_path=archive/'metadata.json';meta=json.loads(meta_path.read_text())
for log,result,program,seed,seconds,d in rows:
    existing=next((r for r in meta['runs'] if r.get('seed')==seed),None)
    if existing is None:
        existing={'seed':seed};meta['runs'].append(existing)
    existing.update({'program':program,'log':log,'result':result,'seconds_requested':seconds,
                     'status':'completed','actual_seconds':d['seconds'],'attempts':d['attempts'],
                     'accepted_moves':d['accepted'],'found_at_most64':False})
    for name in [log,result,program]:
        file=archive/name;meta['files'][str(file)]=hashlib.sha256(file.read_bytes()).hexdigest()
validation={'utc':datetime.now(timezone.utc).isoformat(),'runs':validations,
            'scope':'Final saved states independently scalar-checked; unsuccessful walks prove no lower bound.'}
(archive/'final-scalar-validation.json').write_text(json.dumps(validation,indent=2)+'\n')
for name in ['final-scalar-validation.json','archive_neutral_runs.py']:
    file=archive/name;meta['files'][str(file)]=hashlib.sha256(file.read_bytes()).hexdigest()
meta['finished_utc']=validation['utc']
meta_path.write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps({'runs':[{'seed':seed,'seconds':d['seconds'],'attempts':d['attempts'],
                          'accepted_moves':d['accepted'],'found':False}
                         for log,result,program,seed,seconds,d in rows],
                  'final_scalar_validation':'PASS'}))
