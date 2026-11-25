import json
import sys
from pathlib import Path
pid=int(sys.argv[1])
row={}
for line in Path(f'/proc/{pid}/status').read_text().splitlines():
    name,sep,value=line.partition(':')
    if name in ('VmRSS','VmHWM','RssAnon','RssFile','RssShmem'):
        row[name]=value.strip()
print(json.dumps(row))
