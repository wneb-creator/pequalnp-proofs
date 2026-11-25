from pathlib import Path

edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
edge_set = {tuple(sorted(e)) for e in edges}
edge_masks = [(1<<a)|(1<<b) for a,b in edges]
def adjacent(a,b):
    return tuple(sorted((a,b))) in edge_set
order = [0,1,4,5,2,6,3,9,7,8]
perms = []
def extend(mapping,used):
    if len(mapping)==10:
        perms.append(tuple(mapping[i] for i in range(10)))
        return
    i = order[len(mapping)]
    for j in range(10):
        if j not in used and all(adjacent(i,k)==adjacent(j,v) for k,v in mapping.items()):
            mapping[i]=j
            extend(mapping,used|{j})
            del mapping[i]
extend({},set())
assert len(perms)==120
independent = [m for m in range(1024) if not any((m>>a)&(m>>b)&1 for a,b in edges)]
maximal = [m for m in independent if all(m&(1<<i) or (m|(1<<i)) not in independent for i in range(10))]
representatives = [(3,50),(6,50),(12,50),(3,116),(6,116)]
def rename(mask,perm):
    return sum(1<<perm[i] for i in range(10) if mask&(1<<i))
certs=[]
for edge in edge_masks:
    for mis in maximal:
        matches=[(k,representatives.index(pair)) for k,p in enumerate(perms)
                 if (pair:=(rename(edge,p),rename(mis,p))) in representatives]
        assert matches
        certs.append(min(matches))
assert len(certs)==225
fmt=lambda xs:'['+', '.join(map(str,xs))+']'
lines=['import Mathlib.Data.List.Permutation','import Mathlib.Data.Fintype.Basic','',
       'namespace PEqualNP.Outside.L_meta_2592_aux.OrbitCertificate','',
       'def edgeMasks : List Nat := '+fmt(edge_masks),'',
       'def independentMasks : List Nat := '+fmt(maximal),'',
       'def representatives : List (Nat × Nat) := '+fmt(representatives),'',
       'def permutations : List (List Nat) := [']
lines += ['  '+fmt(p)+(',' if k+1<len(perms) else ']') for k,p in enumerate(perms)]
lines += ['','def witnesses : List (Nat × Nat) := [']
for i in range(15):
    row=', '.join(str(pair) for pair in certs[15*i:15*i+15])
    lines += ['  '+row+(',' if i<14 else ']')]
lines += ['','def renameMask (p : List Nat) (mask : Nat) : Nat :=',
          '  (List.range 10).foldl (fun acc i =>',
          '    if mask.testBit i then acc + 2 ^ (p.getD i 0) else acc) 0','',
          'def adjacent (i j : Nat) : Bool := edgeMasks.contains (2 ^ i + 2 ^ j)','',
          'def preservesGraph (p : List Nat) : Bool :=',
          '  (List.range 10).all fun i => (List.range 10).all fun j =>',
          '    adjacent i j == adjacent (p.getD i 0) (p.getD j 0)','',
          'set_option maxRecDepth 100000 in',
          'set_option maxHeartbeats 800000 in',
          'lemma all_are_permutations :',
          '    ∀ k : Fin 120, (permutations.getD k.val []).Perm (List.range 10) := by',
          '  decide','',
          'set_option maxRecDepth 100000 in',
          'set_option maxHeartbeats 800000 in',
          'lemma all_preserve_graph :',
          '    ∀ k : Fin 120, preservesGraph (permutations.getD k.val []) = true := by',
          '  decide','',
          'set_option maxRecDepth 100000 in',
          'set_option maxHeartbeats 800000 in',
          'lemma five_orbit_witnesses : ∀ (i j : Fin 15),',
          '    let w := witnesses.getD (15 * i.val + j.val) (0, 0)',
          '    let p := permutations.getD w.1 []',
          '    let r := representatives.getD w.2 (0, 0)',
          '    w.1 < 120 ∧ w.2 < 5 ∧',
          '      renameMask p (edgeMasks.getD i.val 0) = r.1 ∧',
          '      renameMask p (independentMasks.getD j.val 0) = r.2 := by',
          '  decide','',
          'end PEqualNP.Outside.L_meta_2592_aux.OrbitCertificate','']
source='\n'.join(lines).replace('import Mathlib.Data.List.Permutation\nimport Mathlib.Data.Fintype.Basic\n\n','').replace('\nlemma ','\ntheorem ')
Path(__file__).with_name('OrbitCertificate.lean').write_text(source)
print('Generated',len(lines),'lines, 120 permutations, 225 witnesses.')
