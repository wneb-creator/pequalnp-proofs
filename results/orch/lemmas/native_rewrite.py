from pathlib import Path
import re
p=Path('/tmp/oec/pequalnp-pilot-182/NativeEngine.lean')
s=p.read_text()
def atom(s,i):
 while s[i].isspace():i+=1
 start=i
 if s[i] in '([':
  ends={'(':')','[':']'}
  stack=[ends[s[i]]];i+=1
  while stack:
   if s[i] in ends:stack.append(ends[s[i]])
   elif s[i]==stack[-1]:stack.pop()
   i+=1
 else:
  while i<len(s) and not s[i].isspace() and s[i] not in '()[],':i+=1
 return s[start:i],i
while 'Bool.rec' in s:
 i=s.rfind('Bool.rec')
 mot,j=atom(s,i+len('Bool.rec'))
 assert mot.startswith('(motive :='),mot
 f,j=atom(s,j);t,j=atom(s,j);d,j=atom(s,j)
 s=s[:i]+'(bif '+d+' then '+t+' else '+f+')'+s[j:]
s=re.sub(r'def st .*?\n', 'def st (n : Nat) (f : Nat → Bool) : Bool := f n\n',s)
s=s.replace('List.rec','listRec').replace('Nat.rec','natRec')
helpers='''
def listRec {α : Type u} {motive : List α → Sort v}
    (nil : motive []) (cons : (a : α) → (as : List α) → motive as → motive (a :: as))
    (xs : List α) : motive xs :=
  match xs with
  | [] => nil
  | a :: as => cons a as (listRec nil cons as)

def natRec {motive : Nat → Sort u} (zero : motive 0)
    (succ : (n : Nat) → motive n → motive (n+1)) (n : Nat) : motive n :=
  match n with
  | 0 => zero
  | n + 1 => succ n (natRec zero succ n)
'''
s=s.replace('namespace Engine','namespace Engine\n'+helpers)
p.write_text(s)
