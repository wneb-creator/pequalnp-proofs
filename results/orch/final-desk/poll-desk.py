import datetime
import json
import pathlib
import subprocess
import time

base = pathlib.Path('/tmp/oec/pequalnp-pilot-143')
url = 'https://pequalnp.com/desk/next?handle=wneb-creator&another=1&hard=1'
end = datetime.datetime(2026, 11, 25, 19, 53, 6, tzinfo=datetime.timezone.utc).timestamp()
next_call = (base / 'desk-recovery-2.json').stat().st_mtime + 240
nulls = 1
index = 0

def stamp():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def state(**kwargs):
    (base / 'poll-state.json').write_text(json.dumps(dict(at=stamp(), nulls=nulls, **kwargs), indent=2) + '\n')

state(status='waiting', next_call_utc=datetime.datetime.fromtimestamp(next_call, datetime.timezone.utc).isoformat())
while time.time() < end:
    remaining = next_call - time.time()
    if remaining > 0:
        time.sleep(min(30, remaining, max(0, end - time.time())))
        continue
    index += 1
    body = base / f'poll-next-{index}.json'
    err = base / f'poll-next-{index}.stderr'
    start = stamp()
    with body.open('wb') as out, err.open('wb') as stderr:
        result = subprocess.run(['curl', '-s', url], stdout=out, stderr=stderr)
    response = body.read_text()
    error_text = err.read_text()
    with (base / 'desk-log.txt').open('a') as log:
        log.write(start + ' POLL REQUEST next another=1 hard=1\n' + stamp() + ' RESPONSE\n' + response + '\n' + error_text + '\n')
    try:
        data = json.loads(response)
        assert isinstance(data, dict)
    except (ValueError, AssertionError):
        data = {'error': 'response was not a JSON object'}
    if result.returncode or 'error' in data:
        diag = base / f'poll-next-{index}-diagnostic.txt'
        diagerr = base / f'poll-next-{index}-diagnostic.stderr'
        with diag.open('wb') as out, diagerr.open('wb') as stderr:
            subprocess.run(['curl', '-si', url], stdout=out, stderr=stderr)
        with (base / 'desk-log.txt').open('a') as log:
            log.write(stamp() + ' DIAGNOSTIC RESPONSE\n' + diag.read_text() + '\n' + diagerr.read_text() + '\n')
        state(status='error_stop', body=str(body), diagnostic=str(diag), message=data.get('error'))
        raise SystemExit(1)
    if data.get('gap') is not None:
        state(status='assigned', body=str(body), gap=data.get('gap', {}).get('id'), lease_present=bool(data.get('lease')))
        raise SystemExit(0)
    nulls += 1
    next_call = time.time() + 240
    state(status='waiting', body=str(body), message=data.get('note', data.get('message')), next_call_utc=datetime.datetime.fromtimestamp(next_call, datetime.timezone.utc).isoformat())
state(status='five_hour_limit', message='Polling window ended without a new assignment.')
