from pathlib import Path
import re,sys,json
source,dest=map(Path,sys.argv[1:3]);s=source.read_text();before=len(s.encode())
helper='''def auditParts (k start n : Nat) : Nat → Prop
 | 0 => auditBlock k start n = true
 | d+1 => auditParts k start (n/2) d ∧ auditParts k (start+n/2) (n-n/2) d
theorem auditParts_all {k start n d} (h : auditParts k start n d) : auditBlock k start n = true := by
 induction d generalizing start n with
 | zero => exact h
 | succ d ih =>
  obtain ⟨hl,hr⟩ := h
  have hh := joinBlock k start (n/2) (n-n/2) (ih hl) (ih hr)
  simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using hh
'''
assert 'def auditParts ' not in s
pos=s.index('\nset_option',s.index('theorem joinBlock '));s=s[:pos]+'\n'+helper+s[pos:]
changed=[]
pattern=re.compile(r'(theorem (blk\d+_\d+)\s*:\s*auditBlock (\d+) (\d+) (\d+)=true := by) decide \+kernel')
def update(m):
 n=int(m.group(5));d=0
 while (n+(1<<d)-1)//(1<<d)>8:d+=1
 if not d:return m.group(0)
 changed.append({'name':m.group(2),'count':n,'depth':d,'max_leaf':(n+(1<<d)-1)//(1<<d)})
 return m.group(1)+'\n apply auditParts_all (d:='+str(d)+')\n simp only [auditParts]\n repeat\' apply And.intro\n all_goals decide +kernel'
s=pattern.sub(update,s);assert changed
if '--compact-colons' in sys.argv[3:]:
 s='\n'.join(l if l.lstrip().startswith('--') else l.replace(' : ',':') for l in s.split('\n'))
dest.write_text(s)
print(json.dumps({'source_bytes':before,'result_bytes':len(s.encode()),'delta':len(s.encode())-before,'blocks_split':len(changed),'max_leaf':max(x['max_leaf'] for x in changed),'result_lines':s.count('\n'),'changes':changed}))
