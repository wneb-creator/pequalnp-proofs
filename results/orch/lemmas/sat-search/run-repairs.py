from pathlib import Path
import subprocess,time,re,json
p=Path('/tmp/oec/pequalnp-pilot-95/sat-search')
prior=p/'cycle13-nott.stdout'
while True:
    if (p/'STOP_SEARCH').exists():raise SystemExit('Stopped before repairs')
    text=prior.read_text() if prior.exists() else ''
    if 'RESULT ' in text:
        if 'RESULT 10 ' in text and not any(line.startswith('OUTPUTS ') for line in text.splitlines()):time.sleep(1);continue
        print(text,flush=True)
        if 'INDEPENDENT_CHECK_ERRORS 0' in text:
            subprocess.run(['python3',str(p/'convert_cycle.py'),str(prior)],check=True)
            raise SystemExit(0)
        break
    time.sleep(1)
def run(name,args):
    with (p/(name+'.stdout')).open('w') as out,(p/(name+'.stderr')).open('w') as err:
        child=subprocess.Popen([str(p/'cycle'),*map(str,args)],stdout=out,stderr=err)
        (p/'active-solver.pid').write_text(str(child.pid)+'\n')
        rc=child.wait()
    text=(p/(name+'.stdout')).read_text()
    match=re.search(r'^RESULT (\d+) elapsed=(\d+)$',text,re.M)
    result={'name':name,'exit_code':rc,'result':int(match.group(1)) if match else None,'seconds':int(match.group(2)) if match else None}
    result['verdict']={0:'UNKNOWN',10:'SAT',20:'UNSAT'}.get(result['result'],'ERROR')
    print(json.dumps(result),flush=True)
    return result,text
r,text=run('cycle-repair-planted14',[14,-1,0,1,60,p/'cycle14-planted.txt',-1,-1])
assert r['result']==10 and 'INDEPENDENT_CHECK_ERRORS 0' in text
summary=[]
for budget in (2,3,4,5):
    if (p/'STOP_SEARCH').exists():raise SystemExit('Stopped between repairs')
    name=f'cycle-repair-budget{budget}'
    result,text=run(name,[13,-1,1,90+budget,60,p/'orbit2-seed958.txt',-1,budget])
    result['budget']=budget;summary.append(result)
    (p/'cycle-repair-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    if result['result']==10:
        assert 'INDEPENDENT_CHECK_ERRORS 0' in text
        subprocess.run(['python3',str(p/'convert_cycle.py'),str(p/(name+'.stdout'))],check=True)
        (p/'cycle-repair-final.stdout').write_text(text)
        raise SystemExit(0)
    if result['result'] not in (0,20):raise SystemExit('Solver failed')
(p/'cycle-repair-final.stdout').write_text('RESULT 0 elapsed=0\nBounded repairs complete with no candidate; no overall SAT verdict.\n')
