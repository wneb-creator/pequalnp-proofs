from pathlib import Path
import argparse,json,time,hashlib

parser=argparse.ArgumentParser(description="Compare packed collision signatures with scalar row checks on a portable fixture.")
parser.add_argument('--fixture',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True,help="Output JSON report filename")
args=parser.parse_args()
start=time.monotonic()
fixture_bytes=args.fixture.read_bytes()
fixture=json.loads(fixture_bytes)
assert fixture['schema']=='packed-collision-fixture-v1'
assert fixture['word_bits']==1024 and fixture['signature_bits']==419
pairs=[tuple(p)for p in fixture['pairs_extended']]
assert len(pairs)==419 and all(0<=r<1024 and 0<=s<1024 for r,s in pairs)
target=int(fixture['target_extended_hex'],16)
assert 0<=target<(1<<1024)
assert all(((target>>r)^(target>>s))&1 for r,s in pairs)
assert [n['node']for n in fixture['nodes']]==[0,52,292,522,5229]
mask1024=(1<<1024)-1;mask419=(1<<419)-1
# The operation ordering is exactly Extended.bin / native signed engine.
def binary(d,a,b,mask):
 if d==0:return a&b
 if d==1:return a|b
 if d==2:return a&(mask^b)
 return(mask^a)&b
def sig(w):return(sum(((w>>r)&1)<<i for i,(r,s)in enumerate(pairs)),sum(((w>>s)&1)<<i for i,(r,s)in enumerate(pairs)))
def cut_profiled(profiles,child):
 for r,s in profiles:
  if ((target>>r)^(target>>s))&1 and all(((w>>r)&1)==((w>>s)&1)for w in child):return True
 return False
results=[]
for fixture_node in fixture['nodes']:
 ni=fixture_node['node'];ws=[int(w,16)for w in fixture_node['bank_extended_hex']];assert len(set(ws))==len(ws);cap=fixture_node['cap'];assert all(0<=w<=mask1024 for w in ws);cache=[sig(w)for w in ws];profiles=[(r,s)for r,s in pairs if sum(((w>>r)^(w>>s))&1 for w in ws)<=2];eligible=cuts=gate_signature_checks=0;rejected={'same':0,'constant':0,'present':0,'length':0}
 for ai,a in enumerate(ws):
  for bi,b in enumerate(ws):
   for d in range(4):
    z=binary(d,a,b,mask1024);zs=(binary(d,cache[ai][0],cache[bi][0],mask419),binary(d,cache[ai][1],cache[bi][1],mask419));assert zs==sig(z);gate_signature_checks+=1
    for ka in [False,True]:
     for kb in [False,True]:
      if a==b:rejected['same']+=1;continue
      if z in(0,mask1024):rejected['constant']+=1;continue
      if z in ws:rejected['present']+=1;continue
      # Exact child list order: z :: kept ka a (kept kb b (erase a, erase b)).
      rest=[w for wi,w in enumerate(ws)if wi not in(ai,bi)]
      if kb:rest=[b]+rest
      if ka:rest=[a]+rest
      child=[z]+rest
      if cap<len(child):rejected['length']+=1;continue
      eligible+=1;coverage=zs[0]^zs[1]
      for wi,w in enumerate(ws):
       if (wi==ai and not ka)or(wi==bi and not kb):continue
       coverage|=cache[wi][0]^cache[wi][1]
      packed_cut=coverage!=mask419;old_cut=cut_profiled(profiles,child);assert packed_cut==old_cut,(ni,ai,bi,d,ka,kb)
      # Scalar check over all419 pairs also validates removing parentprofilefilter.
      assert packed_cut==cut_profiled(pairs,child)
      cuts+=packed_cut
 result={'node':ni,'width':len(ws),'cap':cap,'parent_profile_pairs':len(profiles),'eligible_ordered_children':eligible,'matching_collision_cuts':cuts,'noncuts':eligible-cuts,'gate_signature_checks':gate_signature_checks,'rejected':rejected};results.append(result);print(json.dumps(result),flush=True)
# Invalid pair dictionaries violate the explicit finite good-pairs contract and are rejected.
bad=list(pairs);bad[0]=(bad[0][0],bad[0][0]);assert not all(((target>>r)^(target>>s))&1 for r,s in bad)
assert results==fixture['expected_node_results']
report={'nodes':results,'valid_target_difference_pairs':419,'invalid_pair_contract_rejected':True,'packed_all419_matches_old_profiled_scalar_for_every_eligible_child':True,'all_newgate_signatures_match_direct_rows':True,'elapsed_seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'fixture_sha256':hashlib.sha256(fixture_bytes).hexdigest(),'fixture_provenance':fixture['provenance']};args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'PASS':True,'eligible':sum(x['eligible_ordered_children']for x in results),'cuts':sum(x['matching_collision_cuts']for x in results),'seconds':report['elapsed_seconds']}),flush=True)
