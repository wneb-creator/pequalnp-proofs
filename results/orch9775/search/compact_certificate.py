#!/usr/bin/env python3
"""Trim ASCII LRAT to an independently replayed RUP core and emit Lean."""
import argparse,json,pathlib,math,hashlib

def core(stem):
 stem=pathlib.Path(stem);d=json.loads(stem.with_suffix('.json').read_text());n=len(d['clauses'])
 db={i+1:c for i,c in enumerate(d['clauses'])};hints={};last=None
 for line in stem.with_suffix('.lrat').read_text().splitlines():
  fields=line.split()
  if not fields or fields[1]=='d':continue
  ns=list(map(int,fields));i=ns[0];z=ns.index(0,1);cl=ns[1:z];hs=ns[z+1:-1]
  assert ns[-1]==0 and all(h>0 for h in hs),'RAT hints unsupported'
  assert all(h in db and h<i for h in hs)
  a={-l for l in cl};assert not any(-l in a for l in a),'tautological learned clause'
  assumptions=set(a);reasons={};conflict=False;used=[]
  for h in hs:
   c=db[h];opens=[l for l in c if -l not in a]
   assert len(opens)<=1,(i,h,c,opens)
   used.append(h)
   if not opens:conflict=True;break
   v=opens[0]
   if v not in a:reasons[v]=(h,[-l for l in c if l!=v]);a.add(v)
  assert conflict,('no conflict',i)
  needed={used[-1]};todo=[-l for l in db[used[-1]]];seen=set()
  while todo:
   v=todo.pop()
   if v in assumptions or v in seen:continue
   seen.add(v);rh,deps=reasons[v];needed.add(rh);todo.extend(deps)
  trimmed=[h for h in used if h in needed]
  aa=set(assumptions)
  for j,h in enumerate(trimmed):
   opens=[l for l in db[h] if -l not in aa]
   if not opens:assert j==len(trimmed)-1;break
   assert len(opens)==1;aa.add(opens[0])
  else:raise AssertionError('trimmed reasons lack conflict')
  db[i]=cl;hints[i]=trimmed
  if not cl:last=i;break
 assert last is not None,'no empty clause'
 need={last};todo=[last]
 while todo:
  i=todo.pop()
  for h in hints.get(i,[]):
   if h not in need:need.add(h);todo.append(h)
 base=sorted(i for i in need if i<=n);learn=sorted(i for i in need if i>n and i!=last)
 ids={i:j for j,i in enumerate(base+learn)}
 variables=sorted({abs(l) for i in need for l in db[i]})
 vs={v:j for j,v in enumerate(variables)}
 clause=lambda c:[(vs[abs(l)],l>0) for l in c]
 out={'I':d['I'],'k':d['k'],'no_exact':d.get('no_exact',False),'paired':any(s[0]=='pairedExact' for s in d['schemes']),'facts':[d['facts'][v-1] for v in variables],
  'schemes':[d['schemes'][i-1] for i in base],'book':[clause(db[i]) for i in base+learn],
  'base_count':len(base),'rows':[[ids[h] for h in hints[i]] for i in learn],
  'last_hints':[ids[h] for h in hints[last]],'independent_replay':'all LRAT additions through empty checked, positive RUP hints only',
  'source_cnf_sha256':d['cnf_sha256'],'source_lrat_sha256':hashlib.sha256(stem.with_suffix('.lrat').read_bytes()).hexdigest()}
 return out

def lean_atom(x):return 'true' if x is True else 'false' if x is False else str(x)
def ctor(f):return '('+'.'+f[0]+(' '+' '.join(map(lean_atom,f[1:])) if len(f)>1 else '')+')'
def pack(xs,w):return sum(x<<(w*i) for i,x in enumerate(xs))
def nat(n):return hex(n) if n>1000 else str(n)
MASKS=[127,245,314,432,541,792,1102,1290,1548,2087,2213,2338,4183,4309,4370,4757,5008,5190,5316,6151,6789,7174,7426,7812,8297,8417,8488,8713,9288,9992,10401,10656,12481,13504,14977,16256]
FTAGS=['live','lab','res','common','gate','reader','es','avoid','see','diff']
STAGS=['self','earlier','labCommon','someRes','allRes','exposure','exactAt','avoidLive','seeLive','avoidNot','seeLab','diffX','diffC','adjacentCommon','resCommon','residual','readerAny','readerLive','readerLab','eqLab','gateEq','pairedExact']
def packed_constructor(f,scheme=False):
 tags=STAGS if scheme else FTAGS;tag=tags.index(f[0]);fields=list(f[1:])
 masks={5:1,6:2,7:1,8:2,9:2,10:3,21:4} if scheme else {7:1,8:2}
 if tag in masks:fields[masks[tag]]=MASKS.index(fields[masks[tag]])
 assert all(0<=int(x)<64 for x in fields)
 return tag+sum(int(x)<<(5+6*i) for i,x in enumerate(fields))
def emit(d,name,packed=False,table_size=16,row_size=24):
 I,k=d['I'],d['k'];b=d['base_count'];book=d['book'];N=len(book)
 cw=max(1,(2*len(d['facts'])-1).bit_length());rw=max(1,(N-1).bit_length())
 weak=d['no_exact'];budget=weak and packed
 lines=['import '+('CompactPacking' if packed else 'CompactFramework'),'','namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact',
        'open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution','',
        'def a'+name+' : Array Fact := #['+','.join(map(ctor,d['facts']))+']',
        'def r'+name+' : List Scheme := ['+','.join(map(ctor,d['schemes']))+']','']
 if packed:
  lines[5]='def a'+name+' := (['+','.join(nat(packed_constructor(f)) for f in d['facts'])+'] : List Nat).toArray.map readPackedFact'
  lines[6]='def r'+name+' := (['+','.join(nat(packed_constructor(s,True)) for s in d['schemes'])+'] : List Nat).map '+('readPackedBudget' if budget else 'readPackedScheme')
 packed=[]
 for c in book:
  assert len(c)<64
  packed.append(len(c)+(pack([2*v+int(s) for v,s in c],cw)<<6))
 chunks=[packed[i:i+table_size] for i in range(0,N,table_size)]
 for i,ch in enumerate(chunks):lines.append(f'def table{name}_{i} : List Nat := ['+','.join(map(nat,ch))+']')
 def tree(lo,hi,indent):
  if hi-lo==1:return ' '*indent+f'table{name}_{lo}.getD (i%{table_size}) 0'
  mid=(lo+hi)//2
  return ' '*indent+f'if i < {table_size*mid} then\n'+tree(lo,mid,indent+2)+'\n'+' '*indent+'else\n'+tree(mid,hi,indent+2)
 lines+=['',f'def encoded{name} (i : Nat) : Nat :=',tree(0,len(chunks),2),
         f'def book{name} (i : Nat) : Clause := let n := encoded{name} i; unpackLits {cw} (n%64) (n>>>6)','']
 options=['set_option maxHeartbeats 0 in','set_option maxRecDepth 200000 in']
 if budget:
  init=f'theorem initialClauses{name} : inputsOKBudget {k} {I} a{name} r{name} (baseBook book{name} {b}).toList=true := by decide +kernel'
 elif d['no_exact']:
  # Weak framework API is supplied separately; still emit the checked data.
  init=f'theorem initialClauses{name} : inputsOK {k} {I} a{name} r{name} (baseBook book{name} {b}).toList=true := by decide +kernel'
 else:init=f'theorem initialClauses{name} : inputsOK {k} {I} a{name} r{name} (baseBook book{name} {b}).toList=true := by decide +kernel'
 lines+=options+[init,'']
 rowchunks=[d['rows'][i:i+row_size] for i in range(0,len(d['rows']),row_size)]
 offset=b
 for idx,ch in enumerate(rowchunks):
  enc=[]
  for hs in ch:
   assert hs and len(hs)-1<512
   enc.append((len(hs)-1)+(hs[-1]<<9)+(pack(hs[:-1],rw)<<(9+rw)))
  lines += [f'def rows{name}_{idx} : List Nat := ['+','.join(map(nat,enc))+']']+options+[f'theorem rowsOk{name}_{idx} : checkRows book{name} {rw} {offset} rows{name}_{idx}=true := by decide +kernel','']
  offset+=len(ch)
 hs=d['last_hints'];lines += [f'def lastUnits{name} := digits {rw} {len(hs)-1} {nat(pack(hs[:-1],rw))}']+options+[f'theorem conflict{name} : checkReasons book{name} {N} {hs[-1]} lastUnits{name} 0=true := by decide +kernel','']
 lines+=options+[f'theorem exclude{name} {{D : Dag}} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D'+('≤1' if budget else '=0')+') (bp : Bplus 14 D='+('10' if budget else '11')+f') (eq : mask {I}=ineligSet 14 D) : False := by',
 (f'  obtain ⟨Z⟩ := construct_layout_budget (k:={k}) h hc (by rw [bp]; decide +kernel) eq' if budget else f'  obtain ⟨Z⟩ := construct_layout (k:={k}) h hc bp eq (by decide +kernel)'),
 f'  let v := truth Z a{name}',
 f'  have hbase : ValidThrough v book{name} {b} := '+('book_start_budget' if budget else 'book_start')+f' Z h hc z eq _ _ _ _ initialClauses{name}']
 offset=b;prev='hbase'
 for idx,ch in enumerate(rowchunks):
  offset+=len(ch);lines.append(f'  have h{idx} : ValidThrough v book{name} {offset} := rows_sound {prev} rows{name}_{idx} rowsOk{name}_{idx}');prev=f'h{idx}'
 lines +=[f'  exact book_end {prev} _ _ conflict{name}','end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact','']
 if d['no_exact'] and not budget:
  start=next(i for i,l in enumerate(lines) if l.startswith('theorem exclude'))-2
  lines=lines[:start]+['end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact','']
 return '\n'.join(lines)

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('stem');ap.add_argument('output');ap.add_argument('--name');ap.add_argument('--packed',action='store_true');ap.add_argument('--table-size',type=int,default=16);ap.add_argument('--row-size',type=int,default=24);a=ap.parse_args()
 d=core(a.stem);out=pathlib.Path(a.output);out.parent.mkdir(parents=True,exist_ok=True);out.with_suffix('.json').write_text(json.dumps(d,separators=(',',':'))+'\n');out.with_suffix('.lean').write_text(emit(d,a.name or str(d['I']),a.packed,a.table_size,a.row_size));print(json.dumps({'I':d['I'],'k':d['k'],'base':d['base_count'],'learned':len(d['rows']),'facts':len(d['facts']),'bytes':out.with_suffix('.lean').stat().st_size}))
