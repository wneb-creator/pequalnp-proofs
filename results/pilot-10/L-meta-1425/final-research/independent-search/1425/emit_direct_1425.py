from pathlib import Path
import json,collections,importlib.util,hashlib,time,sys
BASE=Path('/tmp/oec/pequalnp-pilot-10')
WORK=BASE/'independent-search/1425'
SRC=BASE/'single-not-reduction/meta1425'
mode=sys.argv[1] if len(sys.argv)>1 else 'eq'
assert mode in ['eq','tight']
OUT=WORK/f'direct_{mode}';OUT.mkdir(exist_ok=True)
prefixes=['t0-all-eq','t1-all-eq','t2-cap7-all-eq','t3-cap8-all-eq','t4-all-eq','t5-cap8-all-eq','t6-all-eq','t7-all-eq','t8-all-eq','t9-cap8-all-eq'] if mode=='eq' else [f't{i}-final-tight' for i in range(10)]
spec=importlib.util.spec_from_file_location('reviewed_chd',BASE/'fresh-full-proof/meta984/chd.py');chd=importlib.util.module_from_spec(spec);spec.loader.exec_module(chd)
BLOCK=256
# All bound metadata and hashes are untrusted: the final checker retains exact full-state isPerm.
def fld(x,bits,i):return (x>>(bits*i))&((1<<bits)-1)
def pack(xs,bits):return sum(x<<(bits*i) for i,x in enumerate(xs))
def hk(ws):return sum((w+317)**3+1 for w in ws)%4294967291
def natcases(name,vals):return f'def {name} : Nat → Nat\n'+''.join(f'  | {s} => {hex(v) if v>1000 else v}\n' for s,v in sorted(vals.items()) if v)+'  | _ => 0\n'
helpers=(BASE/'independent-search/984/direct_v2/helpers.fragment.lean').read_text()+'''
def qGroupOffset (counts : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => qGroupOffset counts n + fld counts 12 n

def qGroupLocate (counts : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, g, j => (g,j)
  | n+1, g, j =>
    let size := fld counts 12 g
    if j < size then (g,j) else qGroupLocate counts n (g+1) (j-size)

def qGroupNoninputs (initial ws : List Nat) : Nat :=
  ws.countP (fun w => !(initial.contains w))

def qGroupedState (initial : List Nat) (groups valueBits indexBits patterns values counts specs : Nat)
    (records : List (List Nat)) (j : Nat) : List Nat :=
  let slot := qGroupLocate counts groups 0 j
  let g := slot.1
  let localIndex := slot.2
  let spec := fld specs 12 g
  let countBits := spec &&& 3
  let patternBits := (spec >>> 2) &&& 31
  let headerBits := if patternBits = 0 then countBits * initial.length else patternBits
  let width := headerBits + indexBits * g
  let record := fld ((records.getD g []).getD (localIndex/256) 0) width (localIndex%256)
  qDirectStatePattern initial countBits patternBits patterns valueBits indexBits g values record

def qGroupedIndex (initial : List Nat) (counts specs : Nat) (seeds : List Nat) (ws : List Nat) : Nat :=
  let g := qGroupNoninputs initial ws
  let n := fld counts 12 g
  let spec := fld specs 12 g
  let seedBits := (spec >>> 7) &&& 31
  let flag := 2^(seedBits-1)
  let h := hk ws
  let code := fld (seeds.getD g 0) seedBits (h % (max 1 ((n+3)/4)))
  qGroupOffset counts g +
    (if code ≥ flag then code-flag else ((h+code+317)^3 % 11400714819323198549) % n)
'''
(OUT/'helpers.fragment.lean').write_text(helpers)
summary=[];started=time.monotonic()
for graph in [8]+[i for i in range(10) if i!=8]:
 pref=prefixes[graph];meta=json.loads((SRC/(pref+'.meta.json')).read_text());name=f'C{graph}'
 initial=sorted(meta['inputs']);inputset=set(initial);K=len(initial);vb=32
 rowsdict={s:[tuple(json.loads(line)) for line in (SRC/(pref+f'.layer{s}.jsonl')).read_text().splitlines()] for s in range(meta['budget']+1)}
 assert all(tuple(sorted(ws))==ws and all(0<=w<2**32 for w in ws) for rows in rowsdict.values() for ws in rows)
 noninputs=sorted({w for rows in rowsdict.values() for ws in rows for w in ws}-inputset);ib=max(1,len(noninputs).bit_length())
 old={'initial':initial,'dictionary_index_bits':ib,'word_bits':vb,'noninputs':noninputs,'packed_values_hex':hex(pack(noninputs,vb)),'layers':{str(s):{'N':len(rows)} for s,rows in rowsdict.items() if rows}}
 v2={};groups={};allpatterns=set();twopatterns=set();maxgroups=0
 for ss,l in old['layers'].items():
  s=int(ss);bygroup=collections.defaultdict(list)
  rows=rowsdict[s]
  for ws in rows:bygroup[sum(w not in inputset for w in ws)].append(ws)
  for g,rows in bygroup.items():
   maxgroups=max(maxgroups,g+1);patterns=[]
   for ws in rows:
    c=collections.Counter(ws);patterns.append(sum(c[w]<<(2*j) for j,w in enumerate(initial)))
   cb=max(1,max(max(collections.Counter(ws)[w] for w in initial) for ws in rows).bit_length());assert cb<=2
   groups[s,g]={'rows':rows,'patterns':patterns,'count_bits':cb};allpatterns.update(patterns)
   if cb==2:twopatterns.update(patterns)
 candidates=[[],sorted(allpatterns),sorted(twopatterns),v2.get('pattern_codes',[])]
 best=None
 for pats in candidates:
  ps=set(pats);pb=max(1,(len(pats)-1).bit_length());cost=2*K*len(pats)
  choices={}
  for key,g in groups.items():
   use=bool(pats) and set(g['patterns'])<=ps and pb<g['count_bits']*K
   header=pb if use else g['count_bits']*K
   cost+=len(g['rows'])*(header+ib*key[1]);choices[key]=use
  if best is None or cost<best[0]:best=(cost,pats,pb,choices)
 _,patterns,pb,choices=best;pid={p:j for j,p in enumerate(patterns)};patternpack=pack(patterns,2*K)
 params={x:{} for x in ['N','counts','specs']};seedlayers={};recordlayers={};data={'graph':graph,'name':name,'word_bits':vb,'dictionary_index_bits':ib,'initial':initial,'noninputs':old['noninputs'],'packed_values_hex':old['packed_values_hex'],'pattern_codes':patterns,'packed_patterns_hex':hex(patternpack),'groups':maxgroups,'record_block_size':BLOCK,'source_prefix':pref,'target':meta['target'],'budget':meta['budget'],'source_mode':mode,'layers':{}}
 ni={w:j+1 for j,w in enumerate(old['noninputs'])};all_reordered={}
 for s in sorted({s for s,g in groups}):
  sizes=[0]*maxgroups;specs=[0]*maxgroups;seeds=[0]*maxgroups;records=[[] for _ in range(maxgroups)];newrows=[];newgroups={};offset=0
  for g in range(maxgroups):
   if (s,g) not in groups:continue
   source=groups[s,g];rows=source['rows'];cb=source['count_bits'];use=choices[s,g];headerbits=pb if use else cb*K
   width=headerbits+ib*g
   table=chd.build([hk(ws) for ws in rows]);sizes[g]=len(rows);assert len(rows)<4096 and table['bits']<32
   specs[g]=cb+((pb if use else 0)<<2)+(table['bits']<<7)
   seeds[g]=pack(table['codes'],table['bits']);ordered=[None]*len(rows)
   for ws,j in zip(rows,table['positions']):ordered[j]=ws
   recordvalues=[]
   for j,ws in enumerate(ordered):
    c=collections.Counter(ws);pattern=sum(c[w]<<(2*i) for i,w in enumerate(initial))
    header=pid[pattern] if use else pack([c[w] for w in initial],cb)
    others=[ni[w] for w in ws if w not in inputset];assert len(others)==g
    record=header+(pack(others,ib)<<headerbits);recordvalues.append(record)
    inputrecord=fld(patternpack,2*K,header) if use else header
    decoded=[w for i,w in enumerate(initial) for _ in range(fld(inputrecord,2 if use else cb,i))]
    decoded += [old['noninputs'][fld(record>>headerbits,ib,i)-1] for i in range(g)]
    assert sorted(decoded)==list(ws)
    h=hk(ws);code=fld(seeds[g],table['bits'],h%table['buckets']);actual=code-table['flag'] if code>=table['flag'] else chd.mix(h,code,len(rows))
    assert actual==j
   records[g]=[pack(recordvalues[j:j+BLOCK],width) for j in range(0,len(rows),BLOCK)]
   for j,record in enumerate(recordvalues):assert fld(records[g][j//BLOCK],width,j%BLOCK)==record
   newgroups[g]={'N':len(rows),'offset':offset,'countBits':cb,'patternBits':pb if use else 0,'recordBits':width,'seedBits':table['bits'],'flag':table['flag'],'buckets':table['buckets'],'seeds_hex':hex(seeds[g]),'record_blocks_hex':[hex(x) for x in records[g]]}
   offset+=len(rows);newrows.extend(ordered)
  assert len(newrows)==old['layers'][str(s)]['N'];params['N'][s]=len(newrows);params['counts'][s]=pack(sizes,12);params['specs'][s]=pack(specs,12);seedlayers[s]=seeds;recordlayers[s]=records
  all_reordered[s]=newrows
  data['layers'][s]={'N':len(newrows),'packed_counts_hex':hex(params['counts'][s]),'packed_specs_hex':hex(params['specs'][s]),'groups':newgroups}
  (OUT/f'{name}.layer{s}.jsonl').write_text(''.join(json.dumps([hex(w)[2:] for w in ws],separators=(',',':'))+'\n' for ws in newrows))
  # Check actual grouped lookup offset plus rebuilt CHD across every state.
  for j,ws in enumerate(newrows):
   g=sum(w not in inputset for w in ws);n=fld(params['counts'][s],12,g);spec=fld(params['specs'][s],12,g);sb=(spec>>7)&31;flag=1<<(sb-1);h=hk(ws)
   code=fld(seeds[g],sb,h%max(1,(n+3)//4));local=code-flag if code>=flag else chd.mix(h,code,n)
   assert sum(sizes[:g])+local==j
 pieces=[f'def {name}_initial : List Nat := ['+', '.join(hex(w) for w in initial)+']\n',f'def {name}_values : Nat := '+old['packed_values_hex']+'\n',f'def {name}_patterns : Nat := '+hex(patternpack)+'\n']
 pieces += [natcases(name+'_'+key,vals) for key,vals in params.items()]
 pieces.append(f'def {name}_seeds : Nat → List Nat\n'+''.join(f'  | {s} => ['+', '.join(hex(x) for x in row)+']\n' for s,row in sorted(seedlayers.items()))+'  | _ => []\n')
 pieces.append(f'def {name}_records : Nat → List (List Nat)\n'+''.join(f'  | {s} => ['+', '.join('['+', '.join(hex(x) for x in block)+']' for block in row)+']\n' for s,row in sorted(recordlayers.items()))+'  | _ => []\n')
 pieces.append(f'def {name}_S (s j : Nat) : List Nat :=\n  qGroupedState {name}_initial {maxgroups} {vb} {ib} {name}_patterns {name}_values ({name}_counts s) ({name}_specs s) ({name}_records s) j\n')
 pieces.append(f'def {name}_idx (s : Nat) (ws : List Nat) : Nat :=\n  qGroupedIndex {name}_initial ({name}_counts s) ({name}_specs s) ({name}_seeds s) ws\n')
 text='\n'.join(pieces);path=OUT/f'{name}.data.fragment.lean';path.write_text(text)
 (OUT/f'{name}.data.json').write_text(json.dumps(data,indent=2)+'\n')
 diag_s=max((s for s,rows in all_reordered.items() if len(rows)>1),default=meta['budget'])
 (OUT/f'{name}.decoder.fragment.lean').write_text(f'theorem {name}_decoder_diagnostic : qNorm ({name}_S {diag_s} 0) = ['+', '.join(hex(w) for w in all_reordered[diag_s][0])+'] := by decide +kernel\n')
 stat={'graph':graph,'bytes':len(text.encode()),'states':sum(params['N'].values()),'groups':len(groups),'max_groups_per_layer':maxgroups,'patterns':len(patterns),'dictionary_words':len(noninputs),'sha256':hashlib.sha256(text.encode()).hexdigest()}
 summary.append(stat);print(json.dumps(stat),flush=True)
(OUT/'summary.json').write_text(json.dumps(sorted(summary,key=lambda x:x['graph']),indent=2)+'\n')
print(json.dumps({'status':'PASS','states':sum(x['states'] for x in summary),'data_bytes':sum(x['bytes'] for x in summary),'mode':mode,'helpers_bytes':len(helpers.encode()),'seconds':time.monotonic()-started}),flush=True)
