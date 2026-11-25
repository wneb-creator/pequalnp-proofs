from pathlib import Path
import re,json,hashlib,collections,datetime
base=Path('/tmp/oec/pequalnp-pilot-121');mine=base/'not-elimination';files=[Path(x) for x in (mine/'upstream1913-files.txt').read_text().splitlines()]
def clear_comments(s):
 out=list(s);i=0;block=0;line=False;string=False
 while i<len(s):
  if line:
   if s[i]=='\n':line=False
   else:out[i]=' '
   i+=1;continue
  if block:
   if s.startswith('/-',i):out[i:i+2]='  ';block+=1;i+=2;continue
   if s.startswith('-/',i):out[i:i+2]='  ';block-=1;i+=2;continue
   if s[i]!='\n':out[i]=' '
   i+=1;continue
  if string:
   if s[i]=='\\':out[i]=' ';i+=1
   elif s[i]=='"':string=False
   if i<len(s) and s[i]!='\n':out[i]=' '
   i+=1;continue
  if s.startswith('--',i):out[i:i+2]='  ';line=True;i+=2;continue
  if s.startswith('/-',i):out[i:i+2]='  ';block=1;i+=2;continue
  if s[i]=='"':out[i]=' ';string=True
  i+=1
 return ''.join(out)
records=[];failures=[]
for p in sorted(files):
 s=p.read_text();decls=list(re.finditer(r'(?m)^\s*(?:theorem|lemma)\s+PEqualNP\.Outside\.[A-Za-z0-9_]+',s))
 if not decls:failures.append({'file':p.name,'reason':'no full-name final declaration'});continue
 start=decls[-1].start();tail=clear_comments(s[start:]);stack=[];stop=None;assigns=0;topassigns=0;pending_local=0;pairs={'(':')','[':']','{':'}','⟨':'⟩'}
 for i,c in enumerate(tail):
  if c in pairs:stack.append(pairs[c])
  elif stack and c==stack[-1]:stack.pop()
  if not stack and (i==0 or not(tail[i-1].isalnum() or tail[i-1]=='_')) and re.match(r'(?:let|have)\b',tail[i:]):pending_local+=1
  if tail.startswith(':=',i):
   assigns+=1
   if not stack:
    topassigns+=1
    if pending_local:pending_local-=1
    else:stop=i;break
 if stop is None:failures.append({'file':p.name,'reason':'no unbracketed declaration assignment after local lets'});continue
 header=s[start:start+stop].strip();name=re.search(r'PEqualNP\.Outside\.([A-Za-z0-9_]+)',header).group(1)
 records.append({'file':p.name,'theorem':name,'line':s.count('\n',0,start+len(s[start:start+stop])-len(s[start:start+stop].lstrip()))+1,'chars':len(header),'internal_assignments_before_proof':assigns-1,'top_level_internal_assignments_before_proof':topassigns-1,'header':header,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'normalized_text_sha256':hashlib.sha256(s.encode()).hexdigest()})
(mine/'upstream1913-final-statements.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
(mine/'upstream1913-extraction-failures.json').write_text(json.dumps(failures,indent=2)+'\n')
terms=['Monotone2','IsAO2','GateOp.or','GateOp.and','IsReadK','Projective','Incidence','ReadK','Read1','Circuit','TopForm','GateOp.not']
candidates=[r for r in records if any(t in r['header'] for t in terms)]
(mine/'upstream1913-circuit-finals.json').write_text(json.dumps(candidates,ensure_ascii=False,indent=2)+'\n')
exact=[r for r in candidates if re.search(r'Fin\s*\(?\s*(13|26)\b',r['header'])]
(mine/'upstream1913-q3-finals.json').write_text(json.dumps(exact,ensure_ascii=False,indent=2)+'\n')
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'upstream_head':'54bebb6609e633f022b2769684051138160f0906','discovered':len(files),'extracted':len(records),'failures':failures,'headers_with_internal_assignments':sum(r['internal_assignments_before_proof']>0 for r in records),'circuit_candidates':len(candidates),'Fin13_or_Fin26_candidates':len(exact),'q3_names':[r['file'] for r in exact]}
(mine/'upstream1913-census-summary.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2));print('circuit filenames', [r['file'] for r in candidates])
