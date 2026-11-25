"""Preserve the final complementary branch in its own checkpoint directory."""
import datetime,gzip,hashlib,json,shutil
from pathlib import Path

base=Path(__file__).parent;source=base/'checkpoint'
dest=Path('/workspace/pequalnp-proofs/results/orch/final_unused_pair_39')
dest.mkdir(exist_ok=True)
for path in sorted(source.rglob('*')):
    if not path.is_file():continue
    target=dest/path.relative_to(source);target.parent.mkdir(parents=True,exist_ok=True)
    if path.suffix=='.cnf':
        target=target.with_suffix('.cnf.gz')
        with path.open('rb') as incoming,target.open('wb') as outgoing:
            with gzip.GzipFile(filename='',mode='wb',fileobj=outgoing,mtime=0) as compressed:
                shutil.copyfileobj(incoming,compressed)
    else:shutil.copy2(path,target)
for name in ['run.py','publish_checkpoint.py','full-controller.log','control-controller.log','independent-review.txt',
             'used-branch-archive-review.txt']:
    if (base/name).is_file():shutil.copy2(base/name,dest/name)
state='RUNNING'
if (source/'summary.json').exists():
    summary=json.loads((source/'summary.json').read_text())
    if summary['results']:state=summary['results'][-1]['status']
if (base/'full-controller.log').exists():
    text=(base/'full-controller.log').read_text()
    if text.rstrip().endswith('UNKNOWN: retry time or round budget exhausted'):state='UNKNOWN'
used=Path('/workspace/pequalnp-proofs/results/orch/final_retry_pair_39/summary.json')
used_state=json.loads(used.read_text())['results'][-1]['status'] if used.exists() else None
combined=state=='UNSAT_UNUSED_AGGREGATE_BRANCH' and used_state=='UNSAT_STRENGTHENED_MODEL'
legacy=Path('/workspace/pequalnp-proofs/results/orch/star_cut/aggregate.json')
legacy_counts=json.loads(legacy.read_text())
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
(dest/'combined-status.json').write_text(json.dumps({'used_aggregate_branch':used_state,'unused_aggregate_branch':state,
    'original_case39_excluded':combined,'scope':'Original fixed-prefix local family only; no unrestricted circuit bound.',
    'old_excluded_pair_count':legacy_counts['excluded_pair_cases'],
    'combined_excluded_pair_count':legacy_counts['excluded_pair_cases']+int(combined),
    'total_pair_families':legacy_counts['pair_cases'],
    'old_archives_unchanged':True,'snapshot_utc':now},indent=2)+'\n')
(dest/'README.md').write_text('''# Final complementary retry of pair39\n\nThis checkpoint tests the branch in which frozen prefix aggregate wire30 has no readers. Every future selector referencing30 is forbidden; all primaries and every other nonoutput gate must have a reader. The prefix remains exactly the same17 fixed gates and the target budget remains24. Capacity constraints are deliberately omitted because their all-gates-read premise fails. Tail ordering and the reviewed compact blocking constraints are retained.\n\nThe26-gate positive control duplicates the aggregate computation in the variable tail and rewrites former wire30 uses to that duplicate; it passed SAT and full16,384-assignment validation. The target run was authorized only after independent source and assumption review, with at most180 solver seconds. Every SAT candidate is fully validated and any counterexamples are added.\n\nIndependent review established the case partition: earlier prefix gates already have fixed readers; every primary must be read because sampled singleton/edge assignments witness dependence; canonical tail pruning/padding preserves the fixed-prefix model. The normalized model therefore splits into aggregate-used and aggregate-unused branches. UNSAT in both this branch and ../final_retry_pair_39 excludes the original local case39, and only that restricted family. It is external SAT evidence, not a Lean certificate or an unrestricted lower bound.\n\nOld archived counts and manifests remain unchanged. combined-status.json records whether the two reviewed branch results jointly settle the remaining family. Full stdout/stderr, exact commands, source hashes, samples, decoder schemas, metadata and results are preserved. CNFs are losslessly compressed; metadata records their original uncompressed SHA256 hashes.\n\nSnapshot UTC: '''+now+'\nState: '+state+'\nBoth branches UNSAT: '+str(combined)+'\n')
manifest={str(p.relative_to(dest)):hashlib.sha256(p.read_bytes()).hexdigest()
          for p in sorted(dest.rglob('*')) if p.is_file() and p.name!='artifact-manifest.json'}
p=dest/'artifact-manifest.json';p.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'state':state,'both_branches_unsat':combined,'files':len(manifest),
    'manifest_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'snapshot_utc':now},indent=2))
