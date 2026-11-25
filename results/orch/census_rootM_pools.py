from pathlib import Path
from packing_parser import WordFunction,definitions
import sys,json,re,ast
s=Path(sys.argv[1]).read_text();ds=definitions(s);out=Path(sys.argv[2]);w=WordFunction(ds['rootMD11'])
inputs=ast.literal_eval(ds['inputs'].split(':=',1)[1].strip())
cols=ast.literal_eval(ds['rootMCols'].split(':=',1)[1].strip())
assert len(inputs)==9 and all(0<=c[0] and 0<=c[1]<512 for c in cols)
domains=[sum(1<<r for r in range(512) if r&z==0 and r&o==o) for z,o,*_ in cols]
num,depth,cw,offw,lw=1388,4,9,17,0;raw=9;start=num*(10*depth+raw+depth);mask=(1<<512)-1
def bits(pos,n):
 i,sh=divmod(pos,8192);v=w(i)>>sh
 if sh+n>8192:v|=w(i+1)<<(8192-sh)
 return v&((1<<n)-1)
def binval(op,a,b):return [a&b,a|b,a&(~b&mask),(~a&mask)&b][op]
states=[]
for i in range(num):
 rec=bits(i*53,53);ops=rec&((1<<40)-1);bank=list(inputs);choices=[]
 for j in range(depth):
  op=(ops>>(10*j+8))&3;ia=(ops>>(10*j))&15;ib=(ops>>(10*j+4))&15
  a=bank[ia] if ia<len(bank) else 0;b=bank[ib] if ib<len(bank) else 0
  choices.append((op,a,b));bank.append(binval(op,a,b))
 ws=[x for j,x in enumerate(bank) if (rec>>(40+j))&1]
 pos=start+num*offw+bits(start+i*offw,offw);nr=bits(pos,5);rs=[]
 for r in range(nr):
  value=bits(pos+5+r*(cw+depth),cw+depth);ci=value&((1<<cw)-1);paid=value>>cw
  assert ci<len(cols)
  domain=domains[ci];pool=list(inputs);chosen=[c for j,c in enumerate(choices) if paid>>j&1]
  if cols[ci][0]>=512:
   t=cols[ci][0]//512-1;pool.append(binval(t//81,inputs[t//9%9],inputs[t%9]))
  def available(x):
   m=x&domain
   return m==0 or m==domain or any((v&domain)==m for v in pool)
  valid=True
  for op,a,b in chosen:
   if op>=2 or not available(a) or not available(b):valid=False;break
   pool.insert(0,binval(op,a,b))
  if not valid:continue
  c=sum((x&domain) in (0,domain) for x in ws);v=sum(not available(x) for x in ws)
  useful=v<=2 and 10+len(chosen)<=cols[ci][4]+c
  rs.append({'column':ci,'paid':len(chosen),'wires':len(pool),'unavailable':v,'constants':c,'bound':cols[ci][4],'useful':useful})
 states.append({'index':i,'encoded':nr,'valid':len(rs),'useful':sum(r['useful'] for r in rs),'rules':rs})
summary={'source':sys.argv[1],'level':11,'states':num,'encoded_rules':sum(r['encoded'] for r in states),'valid_pools':sum(r['valid'] for r in states),'useful_pools':sum(r['useful'] for r in states),'benchmark_states':states[186:202]}
out.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='benchmark_states'},indent=2))
print(json.dumps([{k:v for k,v in r.items() if k!='rules'} for r in states[186:202]],indent=2))
