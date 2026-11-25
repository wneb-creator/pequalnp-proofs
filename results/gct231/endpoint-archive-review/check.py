from pathlib import Path
import hashlib, json, re
import sympy as s

base=Path('/workspace/pequalnp-proofs/results/gct231')
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def archive(name):
    d=base/name
    entries={}
    for line in (d/'SHA256SUMS').read_text().splitlines():
        h,n=line.split('  ',1); entries[n]=h
        assert sha(d/n)==h,(name,n)
    actual={str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}
    assert actual==set(entries)|{'SHA256SUMS'},(name,actual-set(entries))
    print('ARCHIVE PASS',name,len(entries),sha(d/'SHA256SUMS'),flush=True)
    return d

d=archive('c4-case2-endpoints')
src=(d/'C4Case2Endpoints.lean').read_text()
audit=(d/'C4Case2EndpointsAudit.lean').read_text()
assert audit.startswith(src)
assert audit[len(src):].strip()=='''#print axioms PEqualNP.Outside.L_gct_231.trace.case2_endpoint_one
#print axioms PEqualNP.Outside.L_gct_231.trace.case2_endpoint_sixteen_thirds'''
assert not re.search(r'_root_|"|\bsorry\b|\baxiom\b|native_decide|unsafe|implemented_by|\battribute\b|@\[',src)
assert src.count('set_option maxHeartbeats 1000000 in')==2
assert src.count('theorem ')==2 and src.count('import ')==1
data=json.loads((d/'c4-case2-endpoint-certificate.json').read_text())
U,V=s.symbols('U V'); env={'U':U,'V':V}
e={k:s.sympify(v,locals=env) for k,v in data.items()}
assert s.expand(sum(e[k]*e[k+'_multiplier'] for k in ['q','c','r'])-U)==0
assert s.expand(-e['r']/2+s.Rational(5,2)*U-(V-6))==0
q=4*U**2+2*U*V-3*V**2-48; r=U-3*V-4; l=U*(U-3*V+8)
assert s.expand(l/12-U*r/12-U)==0
assert s.expand(-r/3+U/3-(V+s.Rational(4,3)))==0
assert q.subs({U:0,V:-s.Rational(4,3)})==-s.Rational(160,3)
run=json.loads((d/'case2-endpoints-build01.run.json').read_text())
assert run['status']=='PASS' and run['returncode']==0
log=(d/'case2-endpoints-build01.log').read_text()
assert log.count('depends on axioms:')==2
assert set(re.findall(r'\[(.*?)\]',log,re.S)[0].replace('\n','').replace(' ','').split(','))=={'propext','Classical.choice','Quot.sound'}
print('ENDPOINT PASS: exact rational identities, exact audit source, two explicit conditional scalar statements; no resultant or geometry claim',flush=True)

for name in ['c4-augmented-qq','neogb-qq-reruns']:
    d=archive(name)
    for p in sorted(d.rglob('*.run.json')):
        run=json.loads(p.read_text())
        assert run['status']=='UNKNOWN_OUTPUT_FILE_SIZE_LIMIT' and run['returncode']==-25
        inputs=list(p.parent.glob('*.in'))
        if name=='c4-augmented-qq':
            assert any(sha(q)==run['input_sha256'] for q in inputs)
        assert any(sha(q)==run['companion_sha256'] for q in inputs)
        print('UNKNOWN',p.name,run['wall_seconds'],run['output_file_mib_limit'],flush=True)
    summaries=json.loads((d/'trace-summaries.json').read_text()) if name=='c4-augmented-qq' else [json.loads(p.read_text()) for p in sorted(d.rglob('trace-summary.json'))]
    for info in summaries:
        if 'case' in info: p=d/('case'+str(info['case'])+'.log')
        else:
            parent=d/info['label']; p=next(parent.glob('*.log'))
        complete=[line for line in p.read_text().splitlines() if re.match(r'^\s*\d+\s+\d+\s+\d+\s+\d+\s+x\s+\d+',line) and ' zero' in line and '|' in line]
        assert len(complete)==info['completed_rounds'],(p,len(complete),info['completed_rounds'])
        assert complete[-1]==info['last_completed_round']
        print('ROUND COUNT PASS',p.name,len(complete),flush=True)
print('PASS: archive hashes/coverage, archived companion hashes, augmented native input hashes, resource-limit status and completed-round counts. Rerun native inputs and omitted large trace hashes/payload-comparison measurements are recorded provenance, not independently reread in this review.',flush=True)
