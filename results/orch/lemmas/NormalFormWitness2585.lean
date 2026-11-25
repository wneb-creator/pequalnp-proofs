import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.CircuitMoves PEqualNP.MetaComplexity.NestedCover

abbrev pathIncidence (p l:Fin 2):Prop := l≤p

def pathCNF:Circuit :=
 {gates:=[⟨GateOp.or,[0,1]⟩,⟨GateOp.or,[2,3]⟩,⟨GateOp.and,[4,5]⟩,
   ⟨GateOp.or,[1,2]⟩,⟨GateOp.and,[6,7]⟩],output:=8}

def pathStar:Circuit :=
 {gates:=[⟨GateOp.or,[0,1]⟩,⟨GateOp.and,[2,4]⟩,
   ⟨GateOp.and,[1,3]⟩,⟨GateOp.or,[5,6]⟩],output:=7}

theorem path_no_four:
 ∀p p':Fin 2,∀l l':Fin 2,p≠p'→l≠l'→
 ¬(pathIncidence p l∧pathIncidence p l'∧pathIncidence p' l∧pathIncidence p' l') := by
 decide +kernel

theorem path_cnf_properties:
 IsAO2 4 pathCNF ∧
 (∀z:Fin 4→Bool,circuitFun 4 pathCNF z=decide (∃p l:Fin 2,
   pathIncidence p l∧z (Fin.castAdd 2 p)=true∧z (Fin.natAdd 2 l)=true)) ∧
 (∀g<pathCNF.size,WireBelowOutput 4 pathCNF (4+g)→
   ∀j<pathCNF.size,4+g∈(gateAt pathCNF j).inputs→
   (gateAt pathCNF j).op=GateOp.or∧WireBelowOutput 4 pathCNF (4+j)) ∧
 ¬PEqualNP.ReadK.IsReadK 4 pathCNF 1 := by
 refine ⟨by decide +kernel,by decide +kernel,?_,by decide +kernel⟩
 have dirty:∀g:Fin 4,¬WireBelowOutput 4 pathCNF (4+g.val) := by decide +kernel
 have noReads:∀j:Fin 5,¬8∈(gateAt pathCNF j.val).inputs := by decide +kernel
 intro g hg hbelow j hj hread
 by_cases inner:g<4
 · exact False.elim (dirty ⟨g,inner⟩ hbelow)
 · have eq:g=4 := by change g<5 at hg; omega
   subst g
   exact False.elim (noReads ⟨j,hj⟩ hread)

theorem path_star_properties:
 IsAO2 4 pathStar ∧
 (∀z:Fin 4→Bool,circuitFun 4 pathStar z=circuitFun 4 pathCNF z) ∧
 PEqualNP.ReadK.IsReadK 4 pathStar 1 ∧ pathStar.size<pathCNF.size := by
 decide +kernel

end PEqualNP.Outside.L_meta_2585
