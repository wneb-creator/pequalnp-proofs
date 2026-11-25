from pathlib import Path
import hashlib,json,subprocess,sys
base=Path(sys.argv[1]);prefix=sys.argv[2]
files=subprocess.check_output(['rg','--files',str(base),'-g',prefix+'-best.json','-g',prefix+'-exact-*.json','-g',prefix+'-frontier-*.json','-g',prefix+'-trace-only-*.json','-g',prefix+'-near-*.json'],text=True).splitlines()
initial=[sum(1<<x for x in range(16384) if x>>i&1) for i in range(14)];want=0;positive=[]
for l in range(7):
 for p in [l,(l+1)%7,(l+3)%7]:want|=initial[p]&initial[7+l];positive.append((1<<p)|(1<<(7+l)))
negative=[x for x in range(16384) if not(want>>x&1) and all(want>>(x|(1<<i))&1 for i in range(14) if not(x>>i&1))];assert len(negative)==37
rows=positive+negative;output=[]
for filename in sorted(files):
 raw=Path(filename).read_bytes();d=json.loads(raw);g=d['gates'];v=list(initial);supp=[1<<i for i in range(14)];fan=[0]*(14+len(g));assert d['inputs']==14 and d['marked_inputs']==[0,7] and d['size']==len(g)
 for j,(op,a,b) in enumerate(g):
  assert op in ['and','or'] and a!=b and 0<=a<14+j and 0<=b<14+j
  v.append(v[a]&v[b] if op=='and' else v[a]|v[b]);supp.append(supp[a]&supp[b] if op=='and' else supp[a]|supp[b]);fan[a]+=1;fan[b]+=1
 o=d['output'];assert 0<=o<14+len(g);bits=[i for i,x in enumerate(rows) if bool(v[o]>>x&1)!=(i<21)];traces=[]
 for j,(bv,dv) in enumerate([(0,7),(7,0)]):
  vv=[i==bv for i in range(14)];dd=[i==dv for i in range(14)]
  for op,a,b in g:
   dd.append((dd[a] and vv[b]) or (vv[a] and dd[b]) if op=='and' else dd[a] or dd[b]);vv.append(vv[a] and vv[b] if op=='and' else vv[a] or vv[b])
  traces.append([vv[o],dd[o]])
  if vv[o]:bits.append(58+j)
  if dd[o]:bits.append(60+j)
 assert sorted(bits)==d['failed_bits'],(filename,bits,d['failed_bits'])
 used=set()
 def visit(w):
  if w in used:return
  used.add(w)
  if w>=14:visit(g[w-14][1]);visit(g[w-14][2])
 visit(o);assert sum(w>=14 for w in used)==len(g)
 eligible=bp=bz=0
 for w in used:
  if fan[w]>1:
   if supp[w]:eligible|=supp[w];bp+=fan[w]-1
   else:bz+=fan[w]-1
 falsepos=(v[o]&~want).bit_count();falseneg=(want&~v[o]).bit_count();full=not(falsepos or falseneg or any(a or b for a,b in traces))
 output.append({'file':Path(filename).name,'sha256':hashlib.sha256(raw).hexdigest(),'gates':len(g),'used_inputs':[i for i in range(14) if i in used],'eligible_inputs':[i for i in range(14) if eligible>>i&1],'Bplus':bp,'Bzero':bz,'failed_boundary_bits':sorted(bits),'false_positives':falsepos,'false_negatives':falseneg,'bases_derivatives':traces,'exact_quiet_function':full})
exact=[d['gates'] for d in output if d['exact_quiet_function']]
print(json.dumps({'snapshots':len(output),'truth_rows_each':16384,'boundary_rows':[21,37],'marked_inputs':[0,7],'best_exact_quiet_gates':min(exact) if exact else None,'witnesses_at_most27':sum(n<=27 for n in exact),'validation':'PASS: all reported boundary and derivative error signatures agree with full independent evaluation','results':output},indent=2))
