from pathlib import Path
import subprocess,time,json,re
p=Path('/tmp/oec/pequalnp-pilot-95/sat-search')
prior=p/'full-repair-final.stdout'
while True:
    if (p/'STOP_SEARCH').exists():raise SystemExit('Stopped before fixed-bank batch')
    text=prior.read_text() if prior.exists() else ''
    if 'RESULT ' in text:
        if 'RESULT 10 ' in text and not any(line.startswith('OUTPUTS ') for line in text.splitlines()):
            time.sleep(1)
            continue
        print(text,flush=True)
        if 'INDEPENDENT_CHECK_ERRORS 0' in text:
            subprocess.run(['python3',str(p/'convert_cycle.py'),str(prior)],check=True)
            raise SystemExit(0)
        break
    time.sleep(1)
def run(name,args):
    with (p/(name+'.stdout')).open('w') as out,(p/(name+'.stderr')).open('w') as err:
        child=subprocess.Popen([str(p/'supplied'),*map(str,args)],stdout=out,stderr=err)
        (p/'active-solver.pid').write_text(str(child.pid)+'\n')
        rc=child.wait()
    text=(p/(name+'.stdout')).read_text()
    match=re.search(r'^RESULT (\d+) elapsed=(\d+)$',text,re.M)
    return {'name':name,'exit_code':rc,'result':int(match.group(1)) if match else None,'seconds':int(match.group(2)) if match else None},text
result,text=run('supplied-planted10',[0,1,60,10,p/'supplied-planted10.txt'])
assert result['result']==10 and 'INDEPENDENT_CHECK_ERRORS 0' in text, (result,text)
print('Planted supplied-signal encoder validation passed',flush=True)
summary=[]
for cfg in range(27):
    if (p/'STOP_SEARCH').exists():print('Stopped at configuration',cfg,flush=True);break
    name=f'supplied-config{cfg}'
    result,text=run(name,[cfg,200+cfg,60,7])
    result['configuration']=cfg
    result['verdict']={0:'UNKNOWN',10:'SAT',20:'UNSAT'}.get(result['result'],'ERROR')
    summary.append(result)
    (p/'supplied-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(result),flush=True)
    if result['result']==10:
        assert 'INDEPENDENT_CHECK_ERRORS 0' in text
        subprocess.run(['python3',str(p/'convert_vector7.py'),str(p/(name+'.stdout'))],check=True)
        break
    if result['result'] not in (0,20):raise SystemExit('Solver failed')
