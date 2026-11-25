from pathlib import Path
import subprocess,time,re,json
p=Path('/tmp/oec/pequalnp-pilot-95/sat-search')
prior=p/'cycle-repair-final.stdout'
while True:
    if (p/'STOP_SEARCH').exists():raise SystemExit('Stopped before full repairs')
    text=prior.read_text() if prior.exists() else ''
    if 'RESULT ' in text:break
    time.sleep(1)
summary=[]
for budget,maxnot in ((3,1),(4,3),(5,3)):
    if (p/'STOP_SEARCH').exists():raise SystemExit('Stopped between full repairs')
    name=f'full-repair-budget{budget}-notcap{maxnot}'
    with (p/(name+'.stdout')).open('w') as out,(p/(name+'.stderr')).open('w') as err:
        child=subprocess.Popen([str(p/'synth'),'19','-1',str(maxnot),str(110+budget),'60',str(p/'orbit2-seed19.txt'),str(budget)],stdout=out,stderr=err)
        (p/'active-solver.pid').write_text(str(child.pid)+'\n')
        rc=child.wait()
    text=(p/(name+'.stdout')).read_text();matches=re.findall(r'^RESULT (\d+) elapsed=(\d+)$',text,re.M)
    result={'name':name,'exit_code':rc,'budget':budget,'not_cap':maxnot,'result':int(matches[-1][0]) if matches else None,'seconds':int(matches[-1][1]) if matches else None}
    result['verdict']='SAT' if 'WITNESS\n' in text else 'UNSAT' if result['result']==20 else 'UNKNOWN' if rc==0 else 'ERROR'
    summary.append(result);(p/'full-repair-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(result),flush=True)
    if result['verdict']=='SAT':
        subprocess.run(['python3',str(p/'convert_full.py'),str(p/(name+'.stdout'))],check=True)
        raise SystemExit(0)
    if result['verdict']=='ERROR':raise SystemExit('Full repair failed')
(p/'full-repair-final.stdout').write_text('RESULT 0 elapsed=0\nFull bounded repairs complete with no candidate; no overall SAT verdict.\n')
