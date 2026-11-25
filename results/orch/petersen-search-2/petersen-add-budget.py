from pathlib import Path
from itertools import combinations
import argparse,json,hashlib
parser=argparse.ArgumentParser();parser.add_argument('source',type=Path);parser.add_argument('out',type=Path);parser.add_argument('--budget',type=int,choices=[1,2],required=True);parser.add_argument('--order',choices=['lex','canonical'],default='canonical');args=parser.parse_args()
meta=json.loads(args.source.with_suffix('.json').read_text());s=meta['s'];width=meta['width']
if args.order=='lex':tuples=list(combinations(range(s),args.budget+1))
elif args.budget==1:tuples=[(i,j) for j in range(s) for i in range(j)]
else:tuples=[(i,j,k) for k in range(s) for j in range(k) for i in range(j)]
clauses=[[-(j*width+4) for j in t] for t in tuples]
with args.source.open() as source,args.out.open('w') as out:
 header=source.readline().split();assert header[:2]==['p','cnf'];out.write(f'p cnf {header[2]} {int(header[3])+len(clauses)}\n')
 for line in source:out.write(line)
 for c in clauses:out.write(' '.join(map(str,c))+' 0\n')
meta['clauses']+=len(clauses);meta['budget']=args.budget;meta['budget_clause_order']=args.order;meta['base_sha256']=hashlib.sha256(args.source.read_bytes()).hexdigest();args.out.with_suffix('.json').write_text(json.dumps(meta,indent=2)+'\n')
print('added',len(clauses),'clauses','sha256',hashlib.sha256(args.out.read_bytes()).hexdigest())
