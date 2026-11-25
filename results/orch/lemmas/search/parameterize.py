from pathlib import Path
import re,json
src=Path('/tmp/oec/pequalnp-pilot-184/pr16243-L_meta_10760.lean').read_text()
a=src.index('abbrev Bits := BitVec 1024')
b=src.index('def samplesP21 :')
pre=src[:a]; block=src[a:b]
pat=re.compile(r'(?m)^(?:private )?(abbrev|def|theorem|lemma) ([A-Za-z_][A-Za-z0-9_.\']*)')
matches=list(pat.finditer(block)); decls=[]
for i,m in enumerate(matches):
 end=matches[i+1].start() if i+1<len(matches) else len(block)
 decls.append((m.group(1),m.group(2),block[m.start():end]))
names={name for kind,name,body in decls}
generic={name for kind,name,body in decls if re.search(r'\b1024\b',body)}
while True:
 old=set(generic)
 for kind,name,body in decls:
  if any(re.search(r'(?<![\w.\'])'+re.escape(x)+r'(?![\w.\'])',body) for x in generic):generic.add(name)
 if old==generic:break
aliases={name for kind,name,body in decls if kind=='abbrev' and name in generic}
replpat=re.compile(r'(?<![\w.\'])('+'|'.join(re.escape(x) for x in sorted(generic,key=len,reverse=True))+r')(?![\w.\'])')
def replace(m):
 x=m.group(1)
 return '('+x+' W)' if x in aliases else '('+x+' (W := W))'
out=[]
for kind,name,body in decls:
 m=pat.match(body); assert m
 header=body[:m.end()]
 tail=body[m.end():]
 if name in generic:
  header+=' (W : Nat)' if name in aliases else ' {W : Nat}'
  tail=replpat.sub(replace,tail)
  tail=re.sub(r'\b1024\b','W',tail)
 out.append(header+tail)
result=pre+''.join(out)+'\nend PEqualNP.Outside.L_meta_10760\n'
dest=Path('results/orch/lemmas/search/ParamWidth.lean');dest.write_text(result)
Path('/tmp/oec/pequalnp-pilot-184/search/parameterized-names.json').write_text(json.dumps({'generic':sorted(generic),'aliases':sorted(aliases)},indent=2))
print('generic',len(generic),'aliases',sorted(aliases),'bytes',len(result.encode()))
