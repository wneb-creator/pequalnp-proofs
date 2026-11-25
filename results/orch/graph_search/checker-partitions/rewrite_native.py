from pathlib import Path
import re,sys

def atom(s,p):
 while p<len(s) and s[p].isspace():p+=1
 start=p
 if s[p] in '([{⟨':
  pairs={'(':')','[':']','{':'}','⟨':'⟩'};stack=[pairs[s[p]]];p+=1
  while stack:
   c=s[p]
   if c in pairs:stack.append(pairs[c])
   elif c==stack[-1]:stack.pop()
   p+=1
  return s[start:p],p
 m=re.match(r"[^\s()\[\]{},]+",s[p:])
 if not m:raise ValueError(s[p:p+100])
 return m.group(),p+len(m.group())

src=Path(sys.argv[1]).read_text()
counts={}
for name in ['Bool.rec','List.rec']:
 count=0
 while name in src:
  start=src.rindex(name);p=start+len(name)
  mot,p=atom(src,p)
  if not mot.startswith('(motive :='):raise ValueError((name,mot))
  zero,p=atom(src,p);step,p=atom(src,p);value,p=atom(src,p)
  if name=='Bool.rec':replacement=f'(if {value} then {step} else {zero})'
  else:
   text=step[1:-1] if step.startswith('(') and step.endswith(')') else step
   m=re.fullmatch(r"fun\s+(\S+)\s+(\S+)\s+(\S+)(.*?)=>\s*(.*)",text,re.S)
   if not m:raise ValueError(('step',step))
   a,b,ih,rest,body=m.groups();lazy=f'lazyIH{count}'
   body=re.sub(r"(?<![\w'])"+re.escape(ih)+r"(?![\w'])",f'({lazy} ())',body)
   replacement=f'(lazyListRec {zero} (fun {a} {b} {lazy}{rest} => {body}) {value})'
  src=src[:start]+replacement+src[p:];count+=1
 counts[name]=count

# Unlike Bool.rec, cv is an ordinary strict function call. Delay its final
# argument explicitly; otherwise its guard cannot prune the expensive search.
decl=src.index('def cv ');end=src.index('\ndef ',decl+1)
cv=src[decl:end].replace('(b : Bool)','(b : Unit → Bool)')
lhs,body=cv.split(':=',1)
body=re.sub(r"\bb\b",'(b ())',body)
src=src[:decl]+lhs+':='+body+src[end:]
matches=list(re.finditer(r'\bcv\b',src))
count=0
for match in reversed(matches):
 start=match.start()
 if src[max(0,start-4):start]=='def ':continue
 p=match.end();args=[]
 for _ in range(4):
  a,p=atom(src,p);args.append(a)
 src=src[:start]+'(cv '+' '.join(args[:3])+f' (fun _ => {args[3]}))'+src[p:]
 count+=1
counts['cv']=count

helper='''
def lazyListRec {α β : Type} (z : β)
    (step : α → List α → (Unit → β) → β) : List α → β
  | [] => z
  | x :: xs => step x xs (fun _ => lazyListRec z step xs)

'''
needle='variable {R : ℕ → ℕ}\n'
assert needle in src
src=src.replace(needle,needle+helper,1)
Path(sys.argv[2]).write_text(src)
print(counts)
