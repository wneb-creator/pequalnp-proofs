from pathlib import Path
import argparse,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--exclude',action='append',default=[]);args=ap.parse_args()
p=Path('/tmp/oec/pequalnp-pilot-161')
names=['STRUCTURAL_SEARCH_REPORT.md','reduce-hardcase.py','validate-hardcase.py','inspect-binary-hardcase.py','smt-to-cnf.py','validate-free-model.py','first-or-orbits.py','bipartite-anneal.cpp','cadical-help.txt','cadical-sanity-validation.txt','SEARCH_REPORT.md','SEARCH_REVIEW.md','OR_PRUNING_REVIEW.md','SAT_PIPELINE_REVIEW.md','search-review-small-validation.txt','prune-guard-validation.txt','counterexample-search.cpp','split-search.cpp','dirty-search.cpp','synth.py','freegate-synth.py','augment-raw-pairs.py','batch-split.py','batch-split-results.json','batch-split.log','fano-local.py','update-search-manifest.py']
for pattern in ['hardcase-*','*.cnf','*.cnf.json','*-cadical.log','*-convert.log','*-generate.log','*-sym.smt2','*-sym.smt2.json','*-sym-model.json','*-sym-validation.log','theta-*.log','theta-*.txt','k4subdiv-*.log','k4subdiv-*.txt','counterexample-*.log','split-*.log','dirty-*.log','free-*.log','free-*.smt2','free-*.stdout','synth-*.log','synth-*.smt2','synth-*.stdout','fano-*.cpp','fano-*.log','fano-*.smt2','fano-*.stdout','fano-*.seed.json','fano-*-input.txt','fano-*-validation.txt']:
 names += [f.name for f in p.glob(pattern)]
items=[]
for name in sorted(set(names)):
 if name in args.exclude:continue
 f=p/name
 if f.exists():
  b=f.read_bytes();items.append({'path':str(f),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(p/'search-archive-manifest.json').write_text(json.dumps(items,indent=2))
print('Archive files:',len(items),'bytes:',sum(x['bytes'] for x in items))
