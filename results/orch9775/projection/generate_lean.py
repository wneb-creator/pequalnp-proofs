from pathlib import Path
import json
s=Path('results/orch9775/new-upstream/L_meta_9774.lean').read_text().splitlines();rs=json.loads(Path('results/orch9775/projection/validated-exclusions.json').read_text())['exclude'];o=['import UpstreamGraph','namespace PEqualNP.Outside.L_meta_9775.UpstreamCore','open DagTools']
o+=s[4753:4858]
for r in rs:
 I,P,U,W,J,Q=(r[k] for k in ['I','P','U','W','J','Q']);A=[r['A'].get(str(f),0) for f in range(14)];lhs=J.bit_count()+Q.bit_count()+2*U.bit_count()+W.bit_count()+14-I.bit_count();rhs=P.bit_count()+(P&~I).bit_count()
 o.extend(['set_option maxHeartbeats 0 in','set_option maxRecDepth 100000 in',f'theorem projection{I} {{D : Dag}} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)',f'    (z : Bzero 14 D=0) (eq : mask {I}=ineligSet 14 D) : 12≤Bplus 14 D := by',f'  have v := private_bound h hc z (mask {P}) (mask {I}) (mask {U}) (mask {W}) (mask {J}) (mask {Q})',f'    (fun f : V => mask (({A!s} : List Nat).getD f.val 0)) eq', '    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)', '    (by decide +kernel) (by decide +kernel) (by decide +kernel)',f'  have lhs : (mask {J}).card+(mask {Q}).card+2*(mask {U}).card+(mask {W}).card+(14-(mask {I}).card)={lhs} := by decide +kernel',f'  have rhs : (mask {P}).card+(mask {P} \\ mask {I}).card={rhs} := by decide +kernel','  omega',''])
o.append('end PEqualNP.Outside.L_meta_9775.UpstreamCore');Path('results/orch9775/lemmas/PrivateProjection.lean').write_text('\n'.join(o)+'\n')
