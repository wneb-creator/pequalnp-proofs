"""Lossless witness-format measurements; this does not implement a Lean decoder."""
import collections,gzip,json,math,struct
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-87/library_route')
dag=json.loads((BASE/'signed17-oredge-dag.json').read_text());selected={p:set(v)for p,v in dag['node_ids'].items()};files={'part1':'signed17-oredge-trace.jsonl','part2':'signed17-oredge-part2.jsonl'}
done={};children=collections.defaultdict(list);meta={};proofstates=[];signalwords={}
for part,name in files.items():
 with(BASE/name).open()as f:
  for line in f:
   x=json.loads(line)
   if x['event']=='done'and x['id']in selected[part]:done[(part,x['id'])]=(x['kind'],x['a'],x['b'],x['c'])
   elif x['event']=='signal':signalwords[(part,x['id'])]=int(x['hex'],16)
for part,name in files.items():
 with(BASE/name).open()as f:
  for line in f:
   x=json.loads(line)
   if x['event']!='node'or x['id']not in selected[part]:continue
   key=(part,x['id']);parent=(part,x['parent']);kind=done[key][0]
   if parent in done and done[parent][0]=='expand':children[parent].append(key)
   if kind=='row':meta[key]=10-sum(1<=i<=10 for i in x['state'])
   if kind in('expand','formula0','formula1'):proofstates.append((key,x['remaining'],tuple(signalwords[(part,i)]for i in x['state'])))
rowpairs=collections.Counter();cofpairs=collections.Counter();coftriples=collections.Counter();profiles=collections.Counter();tokens=[];parentstreams=[];naive=bytearray();row_conditional_bits=0
for parent in sorted(children):
 stream=[]
 for key in children[parent]:
  kind,a,b,c=done[key]
  if kind=='row':
   token=('r',a,b);rowpairs[(a,b)]+=1;naive+=struct.pack('<BHH',0,a,b);row_conditional_bits+=7+meta[key]
  elif kind=='cofactor':
   token=('c',a,b);cofpairs[(a,b)]+=1;coftriples[(a,b,c)]+=1;profiles[a]+=1;naive+=struct.pack('<BHIB',1,a,b,c)
  else:
   token=('f',key[0],key[1]);naive+=struct.pack('<BI',2,(key[1]<<1)|(key[0]=='part2'))
  tokens.append(token);stream.append(token)
 parentstreams.append(stream)
def uvar(n):
 out=bytearray()
 while n>=128:out.append((n&127)|128);n>>=7
 out.append(n);return out
ids={t:i for i,t in enumerate(sorted(set(tokens)))}
raw=bytearray();rle=bytearray();profile_stream=bytearray();tag_stream=bytearray();run_counts=[]
for stream in parentstreams:
 raw+=uvar(len(stream));rle+=uvar(len(stream));runs=[]
 for t in stream:
  raw+=uvar(ids[t]);tag_stream.append(0 if t[0] == 'r' else 1 if t[0] == 'c' else 2)
  if t[0]=='c':profile_stream+=uvar(t[1])
  if runs and runs[-1][0]==t:runs[-1]=(t,runs[-1][1]+1)
  else:runs.append((t,1))
 for t,n in runs:rle+=uvar(ids[t]);rle+=uvar(n)
 run_counts.append(len(runs))
dictionary=bytearray()
for t,i in sorted(ids.items(),key=lambda p:p[1]):
 if t[0]=='r':dictionary+=struct.pack('<BHH',0,t[1],t[2])
 elif t[0]=='c':dictionary+=bytes([1])+uvar(t[1])+uvar(t[2])
 else:dictionary+=bytes([2])+uvar((t[2]<<1)|(t[1]=='part2'))
# Reference-only parent streams: recompute each row/cofactor leaf from the child state.
exceptions=bytearray()
for stream in parentstreams:
 refs=[(i,t)for i,t in enumerate(stream)if t[0]=='f'];exceptions+=uvar(len(stream))+uvar(len(refs));last=-1
 for i,t in refs:exceptions+=uvar(i-last-1)+uvar((t[2]<<1)|(t[1]=='part2'));last=i
# Exact standalone state table, with shared truth dictionary, before formula certificates.
words=sorted({w for _,_,state in proofstates for w in state});wordids={w:i for i,w in enumerate(words)};states=bytearray()
for key,remaining,state in proofstates:
 states+=uvar((key[1]<<1)|(key[0]=='part2'))+uvar(remaining)+uvar(len(state))
 for w in state:states+=uvar(wordids[w])
rowids = {v:i for i,v in enumerate(sorted(rowpairs))}
profileids = {v:i for i,v in enumerate(sorted(profiles))}
shortlists = bytearray(); row_list_counts=[]; profile_list_counts=[]
for stream in parentstreams:
 rs=sorted({(t[1],t[2]) for t in stream if t[0]=='r'})
 ps=sorted({t[1] for t in stream if t[0]=='c'})
 row_list_counts.append(len(rs)); profile_list_counts.append(len(ps))
 shortlists += uvar(len(rs)) + uvar(len(ps))
 for r in rs:shortlists += uvar(rowids[r])
 for v in ps:shortlists += uvar(profileids[v])
shortlist_bits=[]
for stream in parentstreams:
 bits=0
 for t in stream:
  if t[0]=='r':bits |= 1 << rowids[(t[1],t[2])]
  elif t[0]=='c':bits |= 1 << (len(rowids)+profileids[t[1]])
 shortlist_bits.append(bits)
width=(len(rowids)+len(profileids)+7)//8
bitset_raw=bytearray();delta_gaps=bytearray();delta_bytes=bytearray();absolute_gaps=bytearray();previous=0
for bits in shortlist_bits:
 bitset_raw += bits.to_bytes(width,'little')
 for value,out in ((bits^previous,delta_gaps),(bits,absolute_gaps)):
  indices=[]
  while value:
   low=value&-value;indices.append(low.bit_length()-1);value-=low
  out += uvar(len(indices));last=-1
  for i in indices:out += uvar(i-last-1);last=i
 delta=(bits^previous).to_bytes(width,'little');nonzero=[(i,v)for i,v in enumerate(delta)if v]
 delta_bytes += uvar(len(nonzero));last=-1
 for i,v in nonzero:delta_bytes += uvar(i-last-1)+bytes([v]);last=i
 previous=bits
# Decode the simple XOR/gap representation and require exact equality.
def readvar(data,pos):
 value=shift=0
 while True:
  b=data[pos];pos+=1;value|=(b&127)<<shift
  if b<128:return value,pos
  shift+=7
pos=0;previous=0;decoded=[]
for _ in shortlist_bits:
 count,pos=readvar(delta_gaps,pos);value=0;last=-1
 for _ in range(count):
  gap,pos=readvar(delta_gaps,pos);last+=gap+1;value |=1<<last
 previous ^=value;decoded.append(previous)
assert decoded==shortlist_bits and pos==len(delta_gaps)
shortlist_dictionary=bytearray()
for p0,n0 in sorted(rowpairs):shortlist_dictionary+=struct.pack('<HH',p0,n0)
for v in sorted(profiles):shortlist_dictionary+=uvar(v)
expanded_states=bytearray()
for key,remaining,state in proofstates:
 if done[key][0]!='expand':continue
 expanded_states += uvar((key[1]<<1)|(key[0]=='part2'))+uvar(remaining)+uvar(len(state))
 for w in state:expanded_states+=uvar(wordids[w])
metrics=dict(expanded_states=len(children),shortlist_bitset_bytes=len(bitset_raw),shortlist_delta_gap_bytes=len(delta_gaps),shortlist_delta_nonzero_bytes=len(delta_bytes),shortlist_absolute_gap_bytes=len(absolute_gaps),shortlist_delta_gap_gzip=len(gzip.compress(delta_gaps,mtime=0)),shortlist_bytes=len(shortlists),shortlist_dictionary_bytes=len(shortlist_dictionary),shortlist_total_bytes=len(shortlists)+len(shortlist_dictionary),shortlist_gzip=len(gzip.compress(shortlist_dictionary+shortlists,mtime=0)),row_shortlist_total=sum(row_list_counts),row_shortlist_max=max(row_list_counts),profile_shortlist_total=sum(profile_list_counts),profile_shortlist_max=max(profile_list_counts),expanded_state_table_bytes=len(expanded_states),expanded_state_table_gzip=len(gzip.compress(expanded_states,mtime=0)),proof_states=len(proofstates),child_records=len(tokens),row_occurrences=sum(rowpairs.values()),unique_row_pairs=len(rowpairs),cofactor_occurrences=sum(cofpairs.values()),unique_cofactor_profile_replay=len(cofpairs),unique_cofactor_profile_replay_mass=len(coftriples),unique_profiles=len(profiles),row_missing_inputs=dict(collections.Counter(meta.values())),conditional_row_bits=row_conditional_bits,unique_tokens=len(ids),dictionary_bytes=len(dictionary),naive_bytes=len(naive),naive_gzip=len(gzip.compress(naive,mtime=0)),varint_stream_bytes=len(raw),varint_stream_gzip=len(gzip.compress(raw,mtime=0)),rle_stream_bytes=len(rle),rle_stream_gzip=len(gzip.compress(rle,mtime=0)),dictionary_plus_varints=len(dictionary)+len(raw),dictionary_plus_rle=len(dictionary)+len(rle),dictionary_plus_varints_gzip=len(gzip.compress(dictionary+raw,mtime=0)),dictionary_plus_rle_gzip=len(gzip.compress(dictionary+rle,mtime=0)),reference_exceptions_bytes=len(exceptions),reference_exceptions_gzip=len(gzip.compress(exceptions,mtime=0)),standalone_state_table_bytes=len(states),standalone_state_table_gzip=len(gzip.compress(states,mtime=0)),state_truth_functions=len(words),literal_truth_dictionary_bytes=128*len(words),profiles_stream_gzip=len(gzip.compress(profile_stream,mtime=0)),tags_stream_gzip=len(gzip.compress(tag_stream,mtime=0)),rle_runs=sum(run_counts),limitations=['Measurements exclude all formula certificates, generic Lean helper code, memo automorphism witnesses, and truth-function derivation programs.','Gzip sizes are a compression benchmark; no Lean gzip decoder is supplied.','Reference-only stream requires a sound generic checker to recompute every omitted row/cofactor leaf.'])
(BASE/'certificate-format-metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
for name,b in [('witness-dictionary.bin',dictionary),('witness-varints.bin',raw),('witness-rle.bin',rle),('witness-exceptions.bin',exceptions),('proof-state-table.bin',states),('witness-shortlists.bin',shortlist_dictionary+shortlists),('expanded-state-table.bin',expanded_states),('witness-shortlist-delta-gaps.bin',delta_gaps),('witness-shortlist-delta-bytes.bin',delta_bytes)]:
 (BASE/name).write_bytes(b)
print(json.dumps(metrics,indent=2))
