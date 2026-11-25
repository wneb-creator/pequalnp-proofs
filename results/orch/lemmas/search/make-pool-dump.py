from pathlib import Path
import re
src=Path('/tmp/oec/pequalnp-pilot-184/replacement/AllComputeDefs.lean').read_text()
groups=[]
for m in re.findall(r'^def check(\d+) ',src,re.M):groups.append(('compact'+m,'grid'+m,'tab'+m,'compactDomains'+m,'poolList'))
for m in re.findall(r'^def ax(\d+)check ',src,re.M):groups.append(('ax'+m,'ax'+m+'G','ax'+m+'T','ax'+m+'D','richPoolList'))
body=['open ComputeBench','','def main : IO Unit := do']
for name,g,t,dom,fn in groups:
 body.extend(['  do',f'    let g := {g}',f'    let t := {t}','    for k in List.range (g.top+1) do','      for i in List.range (t.count k) do','        let state := chartAt g t k i','        let picks := t.picks k i',f'        IO.println s!"PICKS\\t{name}\\t{{k}}\\t{{i}}\\t{{picks}}"','        for pick in picks do',f'          for p in {fn} g.mask {dom} state.2 [pick] do',f'            IO.println s!"POOL\\t{name}\\t{{k}}\\t{{i}}\\t{{pick}}\\t{{p.domain.toNat}}\\t{{p.bound}}\\t{{p.paid}}\\t{{p.wires.map BitVec.toNat}}"'])
Path('/tmp/oec/pequalnp-pilot-184/search/DumpPools.lean').write_text(src+'\n'+'\n'.join(body)+'\n')
print(len(groups),'groups')
