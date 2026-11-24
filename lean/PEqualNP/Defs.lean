import PEqualNP.Defs.Base
import PEqualNP.Defs.Classes
import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Defs.MetaComplexity
import PEqualNP.Defs.MetaComplexityLocal
import PEqualNP.Defs.MetaComplexitySparse
import PEqualNP.Defs.MetaComplexityMinimal
import PEqualNP.Defs.MetaComplexityLgp
import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.Defs.BinaryCircuit
import PEqualNP.Defs.MetaComplexityCoverCircuit
import PEqualNP.Defs.ProofComplexity
import PEqualNP.Defs.ProofComplexityLin
import PEqualNP.Defs.ProofComplexityLinK
import PEqualNP.Defs.ProofComplexityLift
import PEqualNP.Defs.ProofComplexityResK
import PEqualNP.Defs.ProofComplexityRestrict
import PEqualNP.Defs.ProofComplexityBit
import PEqualNP.Defs.ProofComplexityPC
import PEqualNP.Defs.ProofComplexityMoment
import PEqualNP.Defs.ProofComplexityChain
import PEqualNP.Defs.ProofComplexityGeneral
import PEqualNP.Defs.Search
import PEqualNP.Defs.SearchQ
import PEqualNP.Defs.SearchQTree
import PEqualNP.Defs.SearchCP
import PEqualNP.Defs.SearchRUP
import PEqualNP.Defs.SearchQSyn
import PEqualNP.Defs.SearchSoS
import PEqualNP.Defs.Gct
import PEqualNP.Defs.Oracle
import PEqualNP.Defs.Algebraic
import PEqualNP.Defs.Expanders
import PEqualNP.Defs.RiffleRank
import PEqualNP.Defs.TimeAlt
import PEqualNP.Defs.CoverPromise
import PEqualNP.Defs.SingleLevel
import PEqualNP.Defs.DeMorganFormula
import PEqualNP.Defs.MetaComplexityTypedRank
import PEqualNP.Defs.Pebble
import PEqualNP.Defs.Subdivision
import PEqualNP.Defs.AndCountCircuit
import PEqualNP.Defs.PebbleThreeWay
import PEqualNP.Defs.CoLevel
import PEqualNP.Defs.Peelable
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.LiteralPartition
import PEqualNP.Defs.MinimumComplex
import PEqualNP.Defs.PendantBit
import PEqualNP.Defs.BorrowedCoverCircuit
import PEqualNP.Defs.LineDegree
import PEqualNP.Defs.CircuitMoves
import PEqualNP.Defs.LowMerge
import PEqualNP.Defs.NewLowMerge
import PEqualNP.Defs.AffinePlane
import PEqualNP.Defs.EdgeOwnership
import PEqualNP.Defs.PencilGate
import PEqualNP.Defs.BlindGate
import PEqualNP.Defs.BicliqueBlockCost
import PEqualNP.Defs.SharingOrder
import PEqualNP.Defs.NotPremium
import PEqualNP.Defs.NotBracket
import PEqualNP.Defs.PairShadow
import PEqualNP.Defs.InvisibleWire
import PEqualNP.Defs.SharedOr
import PEqualNP.Defs.CleanedNonEdge
import PEqualNP.Defs.MergeCost
import PEqualNP.Defs.CarriedProduct
import PEqualNP.Defs.TopForm
import PEqualNP.Defs.SyntacticMultilinear
import PEqualNP.Defs.TopFormNames

/-!
# The definitions root

This file only gathers the modules of the definitions root, the one part of this project a
recorded statement may speak of (`lean/README.md`). The base definitions (machines, time
bounds, P, NP, reductions) are in `Defs/Base.lean`; each program's own are in its module under
`Defs/`. A program's module may import `PEqualNP.Defs.Base` and the pinned library, never this
file, which imports them all.
-/
