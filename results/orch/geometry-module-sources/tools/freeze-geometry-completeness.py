from pathlib import Path
import hashlib,json,re,shutil
s=Path('/tmp/oec/pequalnp-pilot-62');m=s/'lean-modules'; repo=Path('/workspace/pequalnp-proofs');dst=repo/'results/orch/checked/modules';arc=repo/'results/orch/geometry-module-sources'
status=json.loads((arc/'status.json').read_text()); records=[]
names=[(f'GeometryCompletenessGroup{g}',f'geometry-completeness-group{g}-001.log') for g in range(8)]
names += [('GeometryCompleteness','geometry-completeness-aggregate-001.log'),('GeometryRowsAgreement','geometry-rows-agreement-001.log')]
for n,logname in names:
 log=s/logname
 if not log.exists() or '\nEXIT 0\n' not in log.read_text():continue
 source=m/f'{n}.lean';h=hashlib.sha256(source.read_bytes()).hexdigest()
 shutil.copyfile(source,dst/f'{n}.lean');shutil.copyfile(log,dst/f'{n}.log');(dst/f'{n}.sha256').write_text(h+'  '+n+'.lean\n')
 shutil.copyfile(source,arc/f'{n}.lean');shutil.copyfile(log,arc/'tools'/logname)
 status[n]={'sha256':h,'kernel_checked':True}
 record={'module':n,'sha256':h,'lines':len(source.read_text().splitlines())}
 for k in ['WALL_SECONDS','USER_SECONDS','SYS_SECONDS','PEAK_RSS_KIB','PEAK_CGROUP_BYTES']:
  record[k]=float(re.search(r'^'+k+r' (.+)$',log.read_text(),re.M)[1])
 records.append(record)
(arc/'status.json').write_text(json.dumps(status,indent=2)+'\n')
for n in ['split-geometry-completeness.py','freeze-geometry-completeness.py']:
 shutil.copyfile(s/n,arc/'tools'/n)
(s/'geometry-completeness-checked-summary.json').write_text(json.dumps(records,indent=2)+'\n')
shutil.copyfile(s/'geometry-completeness-checked-summary.json',arc/'tools/geometry-completeness-checked-summary.json')
print(json.dumps(records,indent=2))
