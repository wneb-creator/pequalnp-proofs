from pathlib import Path
import subprocess,time
p=Path('/tmp/oec/pequalnp-pilot-95/sat-search')
while True:
    if (p/'STOP_SEARCH').exists():
        print('Stopped before next slice',flush=True)
        raise SystemExit(0)
    prior=(p/'vector7-13-orab-onenot.stdout').read_text()
    if 'RESULT ' in prior:
        print(prior,flush=True)
        if 'INDEPENDENT_CHECK_ERRORS 0' in prior:
            raise SystemExit(0)
        break
    time.sleep(1)
with (p/'vector7-13-orab-twonot.stdout').open('w') as out,(p/'vector7-13-orab-twonot.stderr').open('w') as err:
    child=subprocess.Popen([str(p/'vector7'),'13','3','-2','53','600'],stdout=out,stderr=err)
    (p/'active-solver.pid').write_text(str(child.pid)+'\n')
    print('Started exactly-two-NOT seven-input slice',flush=True)
    rc=child.wait()
print('Slice exit',rc,flush=True)
print((p/'vector7-13-orab-twonot.stdout').read_text(),flush=True)
