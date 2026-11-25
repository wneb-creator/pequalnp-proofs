from pathlib import Path
import gzip,hashlib,json,re,shutil,sys
p=Path(__file__).resolve().parent;out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
meta=json.loads((p/'run-metadata.json').read_text());check=json.loads((p/'output-audit.json').read_text())
assert meta['exit_code']==-6 and check['verdict']=='PASS_FOR_CHECKPOINT_AND_AVAILABLE_RECORDS'
sha=lambda q:hashlib.file_digest(q.open('rb'),'sha256').hexdigest()
manifest={}
for name in ['rectangles.jsonl','banks.jsonl','completed-weak15.memo','input-weak15.memo']:
 q=p/name;dest=out/(name+'.gz')
 with q.open('rb') as src,dest.open('wb') as raw,gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0,compresslevel=6) as gz:shutil.copyfileobj(src,gz,1024*1024)
 manifest[name]={'original_bytes':q.stat().st_size,'original_sha256':sha(q),'gzip_bytes':dest.stat().st_size,'gzip_sha256':sha(dest)}
for name in ['stdout.txt','stderr.txt','runner-output.txt','run-metadata.json','lineage.json','output-audit.json','output-audit.stderr.txt','audit-initial-parser-failure.txt','run_bounded.py','audit_outputs.py','archive_results.py','copy_search_weak15.cpp','rectangles-v5.txt']:
 q=p/name;shutil.copyfile(q,out/name);manifest[name]={'bytes':q.stat().st_size,'sha256':sha(q)}
text=(p/'stdout.txt').read_text();node=re.findall(r'^nodes=(\d+).*seconds=([0-9.]+)',text,re.M)[-1];count=re.findall(r'^copyclosures=(\d+) entries=(\d+) subchecks=(\d+) subcuts=(\d+)',text,re.M)[-1]
summary={'exit_code':-6,'failure':'std::bad_alloc under configured1GB address-space limit','ordinary_limit':False,'finished_verdicts':re.findall(r'^finished.*$',text,re.M),'last_reported_nodes':int(node[0]),'last_reported_search_seconds':float(node[1]),'wall_seconds':meta['wall_seconds'],'max_rss_kib':meta['max_rss_kib'],'last_reported_closures':int(count[0]),'last_reported_entries':int(count[1]),'last_reported_subchecks':int(count[2]),'last_reported_subcuts':int(count[3]),'checkpoint_weak_states':check['memo_states'],'new_checkpoint_weak_states':check['new_completed_memo_states'],'all15_root_orbits_absent':check['all15_root_orbits_absent'],'missing_signal_footer':check['missing_signal_footer'],'truncated_final_records':check['truncated_final_records']}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(out/'README.md').write_text(f'''Weak15 mono19 first-OR-edge V5 continuation: allocation failure

The process aborted with child exit -6 and std::bad_alloc after
{meta['wall_seconds']:.3f} wall seconds, before its authorized600-second bound.
The supervisor's own exit0 is not the search process's exit status; the child
status is explicit in run-metadata.json. CPU2, a hard1,000,000,000-byte address-space
limit and unchanged800MB estimated-memory guard were used. Peak RSS was
{meta['max_rss_kib']:,}KiB. The hard limit did not get raised or bypassed.

Last progress: {summary['last_reported_nodes']:,} visits at
{summary['last_reported_search_seconds']:.3f} reported seconds. These are the
last reported counts, not an exact final census. No finished-case or circuit
verdict was produced. This failure is not UNSAT or a Lean proof.

The last atomically saved completed-only weak memo contains
{check['memo_states']:,}states, an increase of{check['new_completed_memo_states']:,}
over the61,991-state input. Its full bytes are preserved and audited for context,
record shape, uniqueness and absence of all fifteen edge-OR root orbit images.
No stronger-mode cache was imported. Both memos have exact header:

    PNP_COPY_MEMO_V1 0 19 oredge 1

Input lineage points to the independently reviewed weak15 V3 continuation.
The source/binary are unchanged from that run. The fixed V5 matrix snapshot has
49 extras: the38-record V4 prefix plus11 independently audited symmetry cuts,
in addition to13 built-in matrices. Its exact SHA256 is
 e2c98359c0d903d5b439ec744de076267db30e674cb7e6d75d165337352e7f41.
Matrix/source audits are ../../review-weak15-new-symmetries.txt and
../../review-weak15-resource-guard.txt. The completed strong V3 case is separate.

Allocation failure prevented the final rectangle signal dictionary. The raw
rectangle stream also ends with an incomplete final record, retained exactly.
The audit parses and checks every preceding complete record, accepts malformed
JSON only at the final EOF, reports its exact byte length/hash, and explicitly
marks all unresolved signal IDs. Recorded cost sums are checked arithmetically;
this does not reconstruct every rectangle maximum or signature. All complete
bank histories are replayed on1024 truth rows. There is no complete recursion
proof DAG in these baseline traces. The initial strict-parser failure log is
preserved rather than discarded.

All available stdout/stderr, raw trace bytes, input/output memos, fixed matrices,
source, supervisor, lineage, audit and failure metadata are preserved. Four
streams are deterministically gzip-compressed with raw/packed sizes and hashes
in manifest.json. Decompress beside audit_outputs.py to replay its limited audit.
No automatic restart was attempted.
''')
for name in ['summary.json','README.md']:q=out/name;manifest[name]={'bytes':q.stat().st_size,'sha256':sha(q)}
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(summary,indent=2));print('manifest',sha(out/'manifest.json'),'entries',len(manifest))
