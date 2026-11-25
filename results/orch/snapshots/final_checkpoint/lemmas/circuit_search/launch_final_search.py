"""Launch an approved final profile with a hard planned finish before07:50 UTC."""
import datetime,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
TMP=Path('/tmp/oec/pequalnp-pilot-57')
profile=sys.argv[1]
start=datetime.datetime.now(datetime.timezone.utc)
deadline=start.replace(hour=7,minute=50,second=0,microsecond=0)
duration=int((deadline-start).total_seconds())-10
assert 0<duration<=900
if profile=='punctured':
 binary=TMP/'circuit-search-punctured-essential';log=TMP/'circuit-search-punctured-final.log'
 args=['--feature-costs',str(HERE/'punctured-four-compatibility-tables.txt'),'--polish',str(HERE/'punctured-four-tests.txt'),str(HERE/'punctured-four-stochastic-seeds.txt'),str(duration),'712',str(HERE/'puncturedfinal')]
elif profile=='global':
 binary=TMP/'circuit-search-global-three-champions';log=TMP/'circuit-search-global-three-final.log'
 args=['--polish',str(HERE/'full-singleton-tests.txt'),str(HERE/'global-three-champion-seeds.txt'),str(duration),'713',str(HERE/'globalthreefinal')]
else:raise ValueError(profile)
record=dict(profile=profile,started_utc=start.isoformat(),duration_seconds=duration,planned_stop_utc=(start+datetime.timedelta(seconds=duration)).isoformat(),binary=str(binary),arguments=args,log=str(log))
(HERE/f'{profile}-final-launch.json').write_text(json.dumps(record,indent=2));print(json.dumps(record),flush=True)
with log.open('w') as output:completed=subprocess.run([str(binary),*args],stdout=output,stderr=subprocess.STDOUT,check=False)
record['exit_code']=completed.returncode;record['ended_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
(HERE/f'{profile}-final-completion.json').write_text(json.dumps(record,indent=2));print('completed',completed.returncode,flush=True)
raise SystemExit(completed.returncode)
