from pathlib import Path
import json,sys,itertools,hashlib
p=Path(sys.argv[1]);d=json.loads(p.read_text());g=d['gates'];out=d['output'];D={0,1,3,9}
assert d['input_count']==26 and len(g)==d['active']
assert type(out)is int and 0<=out<26+len(g)
assert g[0]in[[1,0,1],[0,0,13],[1,0,13],[1,2,13]]
for i,(op,a,b)in enumerate(g):assert type(op)is int and op in(0,1)and type(a)is int and type(b)is int and 0<=a<26+i and 0<=b<26+i
rows=[(1<<p)|(1<<(13+l))for p in range(13)for l in range(13)if(p+l)%13 in D]
for k in range(4):
 for s in itertools.combinations(range(13),k):
  t=[l for l in range(13)if all((p+l)%13 not in D for p in s)]
  a=sum(1<<p for p in s);b=sum(1<<l for l in t);rows.extend([a|(b<<13),b|(a<<13)])
rows.extend(1<<i for i in range(26));mask=(1<<len(rows))-1;positive=(1<<52)-1;negative=mask^positive
inputs=[sum(((row>>i)&1)<<k for k,row in enumerate(rows))for i in range(26)]
def evaluate(gs,forced=None,force_value=True):
 w=inputs.copy()
 for i,(op,a,b)in enumerate(gs):w.append((mask if force_value else 0) if i==forced else (w[a]|w[b]if op else w[a]&w[b]))
 return w
w=evaluate(g);target=w[out];bad=[];essential=[];redundant=[];wire_replacements=[]
for i,(op,a,b)in enumerate(g):
 if op or not(w[26+i]&negative):continue
 high=evaluate(g,i)[out];care=high^target
 low=evaluate(g,i,False)[out];fullcare=high^low
 replace=[c for c in range(26+i)if target==(low|(w[c]&fullcare))]
 if replace:wire_replacements.append({"gate":i,"earlier_wires":replace})
 changes=[bool(care&w[a]),bool(care&w[b])];bad.append(i)
 if all(changes):essential.append(i)
 else:redundant.append({'gate':i,'fanin_changes':changes})
print(json.dumps({'file':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'gates':len(g),'fn':(positive^target&positive).bit_count(),'fp':(target&negative).bit_count(),'bad':bad,'essential_bad':essential,'redundant_bad':redundant,'bad_earlier_wire_replacements':wire_replacements}))
