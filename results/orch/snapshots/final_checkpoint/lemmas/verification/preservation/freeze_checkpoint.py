from pathlib import Path
import datetime, gzip, hashlib, json, subprocess, sys
repo=Path('/workspace/pequalnp-proofs')
base=repo/'results/orch'
name=sys.argv[1]
assert name in {'seventh_checkpoint','eighth_checkpoint','ninth_checkpoint','tenth_checkpoint','eleventh_checkpoint','twelfth_checkpoint','final_checkpoint'}
dest=base/'snapshots'/name
assert not dest.exists(), dest
known={}
listing=subprocess.run(['rg','--files','-g','MANIFEST.json','results/orch/snapshots'],cwd=repo,check=True,capture_output=True,text=True).stdout.splitlines()
for path in listing:
    data=json.loads((repo/path).read_text())
    assert isinstance(data,list)
    for row in data:
        known.setdefault(row.get('source',row['file']),set()).add(row['sha256'])
cmd=['rg','--files','-g','*.py','-g','*.cpp','-g','*.json','-g','*.jsonl','-g','*.stdout','-g','*.stderr','-g','*.out','-g','*.err','-g','*.md','-g','*.txt','-g','*.log','-g','*.lean','-g','*.cnf','-g','*.dimacs','-g','*.drat','-g','*.lrat','-g','*.gz','-g','!__pycache__/**','results/orch/lemmas']
listing=subprocess.run(cmd,cwd=repo,check=True,capture_output=True,text=True).stdout.splitlines()
tracked=set(subprocess.run(['git','ls-files','--','results/orch/lemmas'],cwd=repo,check=True,capture_output=True,text=True).stdout.splitlines())
manifest=[]
listed=set(listing)
for source in sorted(listing):
    if source in tracked: continue
    if source + '.gz' in listed: continue
    p=repo/source
    raw=p.read_bytes()
    rel=p.relative_to(base).as_posix()
    sha=hashlib.sha256(raw).hexdigest()
    if sha in known.get(rel,set()): continue
    compressed=len(raw)>500000 and p.suffix != '.gz'
    stored=gzip.compress(raw,mtime=0) if compressed else raw
    target=rel+('.gz' if compressed else '')
    q=dest/target
    q.parent.mkdir(parents=True,exist_ok=True)
    q.write_bytes(stored)
    row={'file':target,'source':rel,'sha256':sha,'bytes':len(raw),'stored_sha256':hashlib.sha256(stored).hexdigest(),'stored_bytes':len(stored)}
    if p.suffix=='.lean': row['status']='untracked experimental source; no compilation claim from this snapshot'
    manifest.append(row)
scratch=Path('/tmp/oec/pequalnp-pilot-57')
log_paths=subprocess.run(['rg','--files','--maxdepth','1','-g','*.log',str(scratch)],cwd=repo,check=True,capture_output=True,text=True).stdout.splitlines()
prefixes=('joint-','circuit-search-joint','full-residual-adaptive','reviewer-','review-joint','prepare-joint','compile-joint','filtered-pair-','saturated-','four-owner-saturation','collinear-','five-owner-','andcount-','and-count-','and13-','and14-','and5-','and6-','and7-','and-skeleton-','forced-active-','packing-','append-star-')
selected_logs=[]
for log_path in sorted(log_paths):
    p=Path(log_path)
    if not p.name.startswith(prefixes): continue
    raw=p.read_bytes(); sha=hashlib.sha256(raw).hexdigest()
    rel='diagnostics/'+p.name
    if sha in known.get(rel,set()): continue
    stored=gzip.compress(raw,mtime=0) if len(raw)>500000 else raw
    target=rel+('.gz' if len(raw)>500000 else '')
    q=dest/target; q.parent.mkdir(parents=True,exist_ok=True); q.write_bytes(stored)
    manifest.append({'file':target,'source':rel,'sha256':sha,'bytes':len(raw),'stored_sha256':hashlib.sha256(stored).hexdigest(),'stored_bytes':len(stored)})
    selected_logs.append(log_path)
(scratch/(sys.argv[1]+'-logs.txt')).write_text('\n'.join(selected_logs)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
dest.mkdir(parents=True,exist_ok=True)
(dest/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
status='''Research preservation checkpoint. L-meta-650 remains unproved and unrefuted; no proof PR or exact-target checker acceptance exists.

This delta freezes changed research programs, candidate banks, finite datasets and complete available diagnostics. Ongoing-run output is complete only through this freeze. Untracked Lean sources are experimental; separately reviewed source commits and successful build logs hold the checked components.

The joint-prefix four-owner model and its concrete assembly/cost checks were independently reviewed. Compatible prefixes preserve the outside cost; additional prefixes must be paid by fewer core gates. The min-five-AND argument applies only to an exact budget-compatible assembly. Generic and concrete four-owner saturation, forced-active restrictions and the weighted bound for ordinary circuits are now Lean-checked and independently reviewed. These remain partial structural results. All current four-owner seeds remain incorrect.

The full residual search now supports bounded gate edits, recentering and retained counterexamples/learned clauses. A local-radius UNSAT does not exclude the unrestricted target. SAT timeouts remain UNKNOWN. Exact finite checks and the full DNF certificate remain mandatory before any candidate is eligible for target assembly.

The five-owner joint prefix packet and exact OR-network cost tables are independently reviewed; core23 plus outside40 suffices, but current seeds are incorrect. The unrestricted-OR thirteen-AND model has separate calibration and scope records: a skeleton alone establishes no total gate budget. Learned-clause retention does not turn UNKNOWN into a proof.

The five-owner dirty five-AND abstraction returned UNSAT both with and without extra pruning. Independent Lean LRAT runtime checks accepted both exact CNF certificates; those compressed proofs and the checker were pushed separately. This is computational CNF validation, not a kernel circuit-encoding theorem. The redundant physical exact-five search was retired after UNKNOWN checkpoints and explicit interruption. A six-AND route remains open.

The complete five-owner AndCount and ordinary-Circuit cleanliness theorems are checked, including correlated OR-feature inputs. A fixed-star raw-core completion proves at least24 gates when there are at mostfive ANDs. The shared-feature paid23 adapter remains separate. Normalized full-plane circuits of size at most63 must have penalty at leastfour; higher penalties remain open.

The global thirteen-AND lower bound is checked; no fifty-one-OR bound or global refutation has been proved. Newly fetched reductions are conditional statements, not established component theorems.

Sub-agents: algebra_strategy, circuit_search, lean_baseline, lower_bound, reduction_analysis, status_review.
'''
mins=(datetime.datetime.now(datetime.timezone.utc)-datetime.datetime(2026,11,25,2,1,8,tzinfo=datetime.timezone.utc)).total_seconds()/60
(dest/'STATUS.md').write_text(status+f'\nTIMING total={mins:.1f} subagents=6\nFrozen UTC: {now}\n')
print(json.dumps({'checkpoint':name,'files':len(manifest),'bytes':sum(r['bytes'] for r in manifest),'stored_bytes':sum(r['stored_bytes'] for r in manifest),'frozen_utc':now,'minutes':round(mins,1)}))
