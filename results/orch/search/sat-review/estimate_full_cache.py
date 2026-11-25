from pathlib import Path
import gzip,json,os,collections,datetime
job=Path('/tmp/oec/pequalnp-pilot-70');out=job/'sat-review';GiB=1<<30
m=json.loads(gzip.decompress((out/'focused-cache-deletions.json.gz').read_bytes()));keep=set(m['focused_modules'])
ledger={}
for f in ['status.json','aux/status.json']:
 for e in json.loads((job/'ram-keeper'/f).read_text())['entries']:ledger[e['path']]=e
regular=[];lost=[]
for e in m['entries']:
 if e['module'] in keep:continue
 if e['reason']=='regenerable_mathlib_artifact_outside_focused_closure':regular.append(e['stat']['size'])
 elif e['reason']=='known_dead_pid_symlink':lost.append(ledger[e['path']]['size'])
fs=os.statvfs('/workspace/pequalnp-proofs/lean');unit=fs.f_frsize
rounded=lambda xs:sum(((s+unit-1)//unit)*unit for s in xs)
logical=sum(regular)+sum(lost);physical=rounded(regular)+rounded(lost)
free=fs.f_bavail*unit;restore_free=782061568
rows=[]
for free_name,space in [('after_focused_cleanup',restore_free),('now',free)]:
 for archive_mib,reserve_mib in [(0,0),(32,128),(64,128),(128,256)]:
  peak=(archive_mib+reserve_mib)*(1<<20)
  pin=max(0,physical-space+peak)
  rows.append({'free_basis':free_name,'batch_archives_MiB':archive_mib,'disk_reserve_MiB':reserve_mib,'pin_bytes':pin,'pin_GiB':pin/GiB,'remaining_of_8GiB_before_other_processes_GiB':8-pin/GiB})
report={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'full_original_cache_completed_modules':9117,'outside_regular_files':len(regular),'outside_regular_logical_bytes':sum(regular),'outside_lost_files':len(lost),'outside_lost_logical_bytes':sum(lost),'full_additional_logical_bytes':logical,'logical_pin_floor_at_cleanup_bytes':max(0,logical-restore_free),'filesystem_fragment_bytes':unit,'rounded_outside_regular_bytes':rounded(regular),'rounded_outside_lost_bytes':rounded(lost),'estimated_full_additional_allocated_bytes':physical,'current_free_bytes':free,'scenarios':rows,'memory_history':{'checker_RSS_KiB':4967096,'checker_RSS_GiB':4967096*1024/GiB,'concurrent_Lean_RSS_KiB':1683736,'concurrent_Lean_RSS_GiB':1683736*1024/GiB,'old_memfd_bytes':5368706264,'old_memfd_GiB':5368706264/GiB,'two_active_solver_RSS_KiB':110780+99300},'limitations':['Allocated-byte estimate rounds each file to filesystem fragments; extents/inodes/directories and possible sparse storage are not in the manifest.','Current free disk may change while agents write.','RSS overlaps shared mappings/page-cache and cannot be added directly to memfd bytes.','The saved checker RSS is a sample, not peak or PSS/private memory; exit137 establishes failure but not a reliable required-memory upper bound.','Removing the baseline avoids irrelevant replay but the savings have not been measured.','Archive peak must be enforced by bounded completed batches; deleting archives does not reduce extracted runtime bytes.']}
(out/'full-cache-resource-estimate.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
