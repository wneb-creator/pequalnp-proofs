import json
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from rup_tools import verify

path, prefix = map(Path, sys.argv[1:3])
deadline = time.monotonic() + int(sys.argv[3])
seen = set()
while time.monotonic() < deadline:
    text = path.read_text() if path.exists() else ''
    lines = text.splitlines()
    if text and not text.endswith('\n'):
        lines = lines[:-1]
    for line in lines:
        if not line.startswith('BEST ') or line in seen:
            continue
        d = json.loads(line[5:])
        valid, length, traces = verify(d['run'])
        assert valid and length == d['length']
        d['traces'] = traces
        d['independently_validated'] = True
        d['validated_at'] = datetime.now(timezone.utc).isoformat()
        result = json.dumps(d, indent=2) + '\n'
        prefix.with_name(prefix.name+f'-best-{length}.json').write_text(result)
        prefix.with_name(prefix.name+'-best.json').write_text(result)
        print(json.dumps(dict(length=length,trial=d['trial'],validated_at=d['validated_at'])),flush=True)
        seen.add(line)
        if length <= 12:
            print('VALIDATED_TARGET_REFUTATION',flush=True)
            sys.exit(0)
    if any(line.startswith('DONE ') for line in lines):
        print('SEARCH_COMPLETE',flush=True)
        sys.exit(0)
    time.sleep(1)
print('WATCH_DEADLINE',flush=True)
