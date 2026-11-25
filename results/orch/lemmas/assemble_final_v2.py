from pathlib import Path
import sys,re,hashlib
p=Path('/tmp/oec/pequalnp-pilot-182')
mods=['KernelFirstEngine','KernelFirstTables','FirstReject','RootShardAdapter','Root13Safe','OwnSequence','OwnRows','ShardCase','ShardTimeCover','CountSplitGlue','GateCatalogue','SymmetryFirst']
mods += [f'FinalBase{i}' for i in [0,1,2,4,5]]
mods += [f'FinalSym{i}' if (p/f'FinalSym{i}.lean').exists() else f'KernelSymCase{i}' for i in range(19)]
mods += ['Root14Safe','ChainFirst','TightNotFirst','TightFinalGlue']
old='PEqualNP.Outside.L_meta_10760_first';new='PEqualNP.Outside.L_meta_10760'
parts=['import PEqualNP.Defs\n\nnamespace '+new+'\n']
for mod in mods:
 s=(p/(mod+'.lean')).read_text()
 lines=[l for l in s.splitlines() if not l.startswith('import ') and l.strip() not in ['namespace '+old,'end '+old]]
 parts.append('\n'.join(lines).strip().replace(old,new).replace('L_meta_10760_first','L_meta_10760')+'\n')
parts.append('end '+new+'\n\n')
parts.append('theorem '+new+' :\n    '+(p/'statement.txt').read_text().strip()+' :=\n  '+new+'.replacement_from_one '+new+'.bound13\n    ('+new+'.live_excluded '+new+'.all_gates_bound)\n')
s='\n'.join(parts)
converted=re.findall(r'^lemma ([^ \n:]+)(?=[^\n]*:= by decide \+kernel\s*$)',s,flags=re.M)
s=re.sub(r'^lemma (?=[^\n]*:= by decide \+kernel\s*$)', 'def ',s,flags=re.M)
(p/'final-numeric-conversions.txt').write_text('\n'.join(converted)+'\n')
# All concrete arithmetic certificates are below the live intake numeral limit.
long=re.findall(r'(?<![\w])(?:0x[0-9a-fA-F]+|[0-9]+)(?![\w])',s)
assert not [n for n in long if len(n.removeprefix('0x'))>20]
assert '_root_' not in s and '"' not in s
assert len(s.encode())<=512*1024
out=Path(sys.argv[1]) if len(sys.argv)>1 else p/'FinalSafeCandidate.lean'
out.write_text(s)
print(out.name,'lines',len(s.splitlines()),'bytes',len(s.encode()),'sha256',hashlib.sha256(s.encode()).hexdigest())
(p/'final-assembly-modules.txt').write_text('\n'.join(mods)+'\n')
