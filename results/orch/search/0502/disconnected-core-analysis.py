from pathlib import Path
import importlib.util,json,hashlib,bisect,collections
B=Path('/tmp/oec/pequalnp-pilot-21/search')
source=B/'cegis-disconnected-five-supported.py'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='1d5fa0b215a8cde4c7277cd348e3fc2481473317fd39205b489a77eeb11f52f2'
spec=importlib.util.spec_from_file_location('core_review',source);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Count(m.f.b.CNF):
 def __init__(self):self.n=0;self.count=0
 def add(self,*xs):self.count+=1
c=Count();events=[(1,'structure',None)]
original=m.row_values
calls=0
def rows(c,ops,aa,bb,mask):
 global calls
 events.append((c.count+1,'band' if calls<3003 else 'extreme',mask));calls+=1
 return original(c,ops,aa,bb,mask)
m.row_values=rows
old_support=m.parent_support_guards
def support(c,*args):
 events.append((c.count+1,'shared_parent_support',None));result=old_support(c,*args);events.append((c.count+1,'output_support',None));return result
m.parent_support_guards=support
m.encode(c,m.f.ROWS)
assert c.n==129309 and c.count==2676975 and calls==3029
# Final130 label-guarded global-upper/nonordinary clauses follow row semantics.
events.append((c.count-130+1,'extreme_output_conditions',None));events.sort()
needed=[]
with (B/'disconnected-rup-0459/checked/needed-original-clauses.txt').open() as f:
 for line in f:needed.append(int(line.split(maxsplit=1)[0]))
starts=[x[0] for x in events];counts=collections.Counter();rowcounts=collections.Counter()
for ident in needed:
 _,kind,mask=events[bisect.bisect_right(starts,ident)-1];counts[kind]+=1
 if mask is not None:rowcounts[(kind,mask)]+=1
report={'scope':'Clause-dependency statistics only; no new satisfiability claim','needed_originals':len(needed),'counts_by_phase':dict(counts),'distinct_band_rows':sum(k=='band' for k,m in rowcounts),'distinct_extreme_rows':sum(k=='extreme' for k,m in rowcounts),'rows':[{'kind':k,'mask':mask,'true_points':[p for p in range(13) if mask>>p&1],'needed_clauses':n} for (k,mask),n in sorted(rowcounts.items())]}
(B/'disconnected-core-analysis.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='rows'}))
