from pathlib import Path
import subprocess,time
p=Path('/tmp/oec/pequalnp-pilot-95/sat-search')
prior=p/'vector7-13-orab-twonot.stdout'
while True:
    if (p/'STOP_SEARCH').exists():raise SystemExit('Stopped before second-orbit slice')
    text=prior.read_text() if prior.exists() else ''
    if 'RESULT ' in text:
        if 'RESULT 10 ' in text and not any(line.startswith('OUTPUTS ') for line in text.splitlines()):
            time.sleep(1)
            continue
        print(text,flush=True)
        if 'INDEPENDENT_CHECK_ERRORS 0' in text:
            subprocess.run(['python3',str(p/'convert_vector7.py'),str(prior)],check=True)
            raise SystemExit(0)
        break
    time.sleep(1)
def run(name,args):
    with (p/(name+'.stdout')).open('w') as out,(p/(name+'.stderr')).open('w') as err:
        child=subprocess.Popen([str(p/'cycle'),*map(str,args)],stdout=out,stderr=err)
        (p/'active-solver.pid').write_text(str(child.pid)+'\n')
        rc=child.wait()
    text=(p/(name+'.stdout')).read_text()
    print(name,'exit',rc,flush=True);print(text,flush=True)
    return text
text=run('cycle14-planted',[14,-1,0,1,60,p/'cycle14-planted.txt'])
assert 'RESULT 10 ' in text and 'INDEPENDENT_CHECK_ERRORS 0' in text
subprocess.run(['python3',str(p/'convert_cycle.py'),str(p/'cycle14-planted.stdout'),'20'],check=True)
text=run('cycle13-nott',[13,-1,1,83,600,'',6])
if 'INDEPENDENT_CHECK_ERRORS 0' in text:subprocess.run(['python3',str(p/'convert_cycle.py'),str(p/'cycle13-nott.stdout')],check=True)
