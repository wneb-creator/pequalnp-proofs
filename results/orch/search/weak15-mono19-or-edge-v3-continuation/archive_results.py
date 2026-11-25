from pathlib import Path
import gzip,hashlib,json,re,shutil,sys
p=Path(__file__).resolve().parent
out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
meta=json.loads((p/'run-metadata.json').read_text());assert 'exit_code' in meta
check=json.loads((p/'output-audit.json').read_text());assert check['verdict']=='PASS'
sha=lambda q:hashlib.file_digest(q.open('rb'),'sha256').hexdigest()
manifest={}
for name in ['rectangles.jsonl','banks.jsonl','completed-weak15.memo','input-weak15.memo']:
 q=p/name;dest=out/(name+'.gz')
 with q.open('rb') as src,dest.open('wb') as raw,gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0,compresslevel=6) as gz:shutil.copyfileobj(src,gz,1024*1024)
 manifest[name]={'original_bytes':q.stat().st_size,'original_sha256':sha(q),'gzip_bytes':dest.stat().st_size,'gzip_sha256':sha(dest)}
for name in ['stdout.txt','stderr.txt','runner-output.txt','run-metadata.json','lineage.json','output-audit.json','output-audit.stderr.txt','run_bounded.py','audit_outputs.py','archive_results.py','copy_search_weak15.cpp','rectangles-v3.txt']:
 q=p/name;shutil.copyfile(q,out/name);manifest[name]={'bytes':q.stat().st_size,'sha256':sha(q)}
text=(p/'stdout.txt').read_text();lastnodes=re.findall(r'^nodes=(\d+).*seconds=([0-9.]+)',text,re.M)[-1]
lastcounts=re.findall(r'^copyclosures=(\d+) entries=(\d+) subchecks=(\d+) subcuts=(\d+) memory_estimate=(\d+).*projection_resets=(\d+)',text,re.M)[-1]
summary={'exit_code':meta['exit_code'],'ordinary_limit':'limit reached' in text,'finished_verdicts':re.findall(r'^finished.*$',text,re.M),'reported_nodes':int(lastnodes[0]),'reported_search_seconds':float(lastnodes[1]),'wall_seconds':meta['wall_seconds'],'max_rss_kib':meta['max_rss_kib'],'copyclosures':int(lastcounts[0]),'entries':int(lastcounts[1]),'subchecks':int(lastcounts[2]),'subcuts':int(lastcounts[3]),'final_memory_estimate':int(lastcounts[4]),'projection_resets':int(lastcounts[5]),'completed_weak_states':check['memo_states'],'new_completed_weak_states':check['new_completed_memo_states'],'root_in_completed_memo':check['root_in_completed_memo']}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');manifest['summary.json']={'bytes':(out/'summary.json').stat().st_size,'sha256':sha(out/'summary.json')}
readme=f'''Weak15 mono19 first-OR-edge V3 continuation

This is a bounded 600-second computational continuation of the independently
reviewed fresh weak15 benchmark in ../weak15-mono19-or-edge. It imports only
that run's 26,439 completed weak-mode states, whose full input memo is retained
here and whose exact SHA256 is recorded in lineage.json. No stronger-mode memo
was imported. The unchanged loader recanonicalizes input states. The memo
context is PNP_COPY_MEMO_V1 0 19 oredge 1; its final 1 denotes weak15 mode.
All 1,145 effective cofactor bounds equal their signed-table values.

The fixed, independently reviewed V3 matrix input contains 26 extra matrices
(six LP plus twenty symmetry records), in addition to thirteen built-in ones.
Its SHA256 is37e6f09e1de3891bd41d299717abff53f830f5d804b57659bad59478f1f3d1e5.
This exact snapshot was used throughout; V4 was not used.

Outcome: {summary['reported_nodes']:,} new visited nodes in
{summary['reported_search_seconds']:.3f} reported search seconds and
{meta['wall_seconds']:.3f} wall seconds; process exit {meta['exit_code']}.
The completed weak memo now contains {check['memo_states']:,} states,
an increase of {check['new_completed_memo_states']:,}. Root present in completed
memo: {check['root_in_completed_memo']}. Ordinary limit: {summary['ordinary_limit']}.
Finished-case verdicts: {summary['finished_verdicts']}.
This archive is computational evidence, not a Lean proof or an UNSAT claim
from a resource limit. The complete raw stdout/stderr and structured summary
supply the exact outcome.

The supervisor enforces one CPU, lower scheduling priority, and a
1,000,000,000-byte address-space limit; peak RSS was {meta['max_rss_kib']:,} KiB.
The source is byte-identical to the reviewed fresh weak15 source; its only
difference from the reviewed dynamic baseline is two memory stopping guards
lowered from1.5GB to800MB. Source review: ../../review-weak15-resource-guard.txt.
Input-archive review: ../../review-weak15-archive.txt.

All emitted rectangle and bank records, completed memo, input memo, source,
fixed matrix file, invocation/resource metadata, lineage and audit are retained.
These emitted traces are not a full recursion proof DAG. Future kernel replay
must export and validate proof dependencies; this memo alone cannot supply them.
The audit checks exact lineage hashes/context, profile bounds, trace arithmetic,
input-row polarity, every emitted bank history, and memo shape/uniqueness/root.
It does not recompute every rectangle maximum or reprove the cofactor bounds.

manifest.json records full raw and deterministic gzip sizes and SHA256 hashes.
Decompress the four gzip streams beside audit_outputs.py and run that script to
repeat the audit. run-metadata.json records the exact command and binary hash.
The source can be compiled with g++ -O3 -std=c++20 as in the preceding archive.
'''
(out/'README.md').write_text(readme);manifest['README.md']={'bytes':(out/'README.md').stat().st_size,'sha256':sha(out/'README.md')}
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(summary,indent=2));print('manifest',sha(out/'manifest.json'),'entries',len(manifest))
