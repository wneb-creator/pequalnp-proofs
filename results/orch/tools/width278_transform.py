from pathlib import Path
import argparse, hashlib, json, re
p=argparse.ArgumentParser();p.add_argument('source');p.add_argument('output');p.add_argument('--report');a=p.parse_args()
s=Path(a.source).read_text();i=s.index('def g15d3 ');prefix,tail=s[:i],s[i:]
allowed={'Bits','pairSig','properPairs','pair_sep','faithful','asRow','asRow_bit','bit_vertex','bit_liftGoal','evalMove','evalMove_sound','chart_bit','chart_pairs','graphValid','lanePlace','laneSmall','place_and','place_or','place_xor','fullMarks','unit_bit','guardBit','mark_at','onMarks','marked_ok','batchMove_at'}
owner=None;changes=[];out=[]
for lineno,line in enumerate(prefix.splitlines(keepends=True),1):
 m=re.match(r'(?:(?:private|noncomputable|protected)\s+)*(?:def|abbrev|theorem|lemma) ([\w.]+)',line)
 if m:owner=m.group(1)
 if re.search(r'\b(?:768|769)\b',line):
  assert owner in allowed,(lineno,owner)
  new=re.sub(r'\b(?:768|769)\b',lambda m:'278' if m.group()=='768' else '279',line)
  changes.append({'line':lineno,'declaration':owner,'before':line.rstrip(),'after':new.rstrip()});line=new
 out.append(line)
result=''.join(out)+tail
assert result[result.index('def g15d3 '):]==tail
assert re.findall(r'\b512\b',result)==re.findall(r'\b512\b',s)
assert 'abbrev Sig := BitVec 512' in result
assert 'abbrev Bits := BitVec 278' in result
Path(a.output).write_text(result)
r={'input':a.source,'output':a.output,'input_sha256':hashlib.sha256(s.encode()).hexdigest(),'output_sha256':hashlib.sha256(result.encode()).hexdigest(),'certificate_suffix_sha256':hashlib.sha256(tail.encode()).hexdigest(),'certificate_suffix_byte_identical':True,'all_512_tokens_preserved':True,'changed_lines':len(changes),'changes':changes}
if a.report:Path(a.report).write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k!='changes'}))
