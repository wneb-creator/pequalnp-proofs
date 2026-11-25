from pathlib import Path
import json,collections,hashlib,time
from fractions import Fraction
base=Path('/tmp/oec/pequalnp-pilot-78');out=base/'construct_search';folder=base/'numeric/s4-structure';chart=json.loads((base/'numeric/s4-hadamard/chart.json').read_text());mapping=json.loads((folder/'rational-id-rowmap.json').read_text());certpath=folder/'graded-rational-id-certificates.jsonl';cs=[json.loads(line) for line in certpath.read_text().splitlines()];start=time.monotonic();reports=[]
for record in cs:
 target={tuple(mapping['columns'][j]):Fraction(co) for j,co in record['polynomial']};actual=collections.defaultdict(Fraction)
 for index,weight in record['certificate']:
  gen,mul=mapping['rows'][mapping['order'][index]];weight=Fraction(weight)
  for mon,co in chart['polynomials'][gen]:actual[tuple(sorted(mul+mon))]+=weight*co
 actual={m:co for m,co in actual.items() if co};assert actual==target,record['target'];assert max(map(len,actual))<=4
 reports.append({'target':record['target'],'certificate_rows':len(record['certificate']),'terms':len(target),'max_degree':max(map(len,target))})
report={'verdict':'PASS exact rational independent raw-generator expansion','count':len(reports),'source_sha256':hashlib.sha256(certpath.read_bytes()).hexdigest(),'seconds':time.monotonic()-start,'targets':reports};(out/'unaveraged-quartics-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='targets'}))
