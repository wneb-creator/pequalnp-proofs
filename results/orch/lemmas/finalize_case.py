from pathlib import Path
import sys,re,json
p=Path('/tmp/oec/pequalnp-pilot-182')
label=sys.argv[1]
kind='Base' if label.startswith('base') else 'Sym'
i=int(label[4:] if kind=='Base' else label[3:])
source=p/f'Strict{kind}{i}.lean'
s=source.read_text()
s=re.sub(r'^lemma (?=[^\n]*:= by decide \+kernel\s*$)', 'def ',s,flags=re.M)
exceptions={'base0':[5,65],'sym6':[47],'sym9':[46]}.get(label,[])
if exceptions:
 s=s.replace('import ShardCase','import ShardCase\nimport CountSplitGlue')
 d=json.loads((p/f'advanced-strict-{label}.json').read_text())
 expr=re.search(r'noncomputable def run_'+label+r' \(p : Nat × Nat\) : Bool :=\n  ([^\n]+)',s).group(1)
 for residue in exceptions:
  j=next(j for j,x in enumerate(d['shards']) if x['H']==1<<residue and x['ph']==0)
  pair=f'(((2 ^ 1 - 1) <<< {residue}), 0)'
  nm=f'count_{label}_{residue}'
  ex=expr.replace('(List.range 13)','ts').replace('p.1',f'((2 ^ 1 - 1) <<< {residue})').replace('p.2','0')
  block=f'noncomputable def {nm} (ts : List Nat) : Bool :=\n  {ex}\n'
  terms=[]
  for tag,ts in [('zero','[0]'),('one','[1]'),('more','((List.range 13).drop 2)')]:
   term=f'{nm}_{tag}';terms.append(term)
   block+=f'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ndef {term} : {nm} {ts} = false := by decide +kernel\n'
  block+=f'def split_{label}_{j} : run_{label} {pair} = false :=\n  chkT_count_split '+ ' '.join(terms)+'\n'
  pattern=r'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\ndef split_'+label+'_'+str(j)+r' : [^\n]+\n'
  s,n=re.subn(pattern,lambda _:block,s)
  assert n==1,(label,residue,j,n)
(p/f'Final{kind}{i}.lean').write_text(s)
print('Final'+kind+str(i),len(s.encode()))
