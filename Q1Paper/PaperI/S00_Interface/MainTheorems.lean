
import Q1Paper.Basic
import Q1Paper.RankIdentity
import Q1Paper.RankIdentityMatrix
import Q1Paper.Compression
import Q1Paper.CompressionIdentity
import Q1Paper.RankAdditivity
import Q1Paper.RowSpaceAlgebraic
import Q1Paper.SubspaceQuotient
import Q1Paper.KappaObs
import Q1Paper.FreeRows
import Q1Paper.SubspaceProjection
import Q1Paper.ConstantRankPencil
import Q1Paper.RowEqualityStep
import Q1Paper.BoundLower
import Q1Paper.Monotone
import Q1Paper.MonotoneBlocks
import Q1Paper.RankConsistency
import Q1Paper.GramRankAugmented
import Q1Paper.BezoutDeg
import Q1Paper.BezoutReal
import Q1Paper.SpectralCertificate
import Q1Paper.Window
import Q1Paper.LeftInverseAdjugate
import Q1Paper.LeftInverse
import Q1Paper.LeftInverseCoefficient
import Q1Paper.DegreeBounds
import Q1Paper.FixedOrder
import Q1Paper.FPT
import Q1Paper.PaperI.S00_Interface.Interface
import Q1Paper.PaperI.S01_Compression.CompressionMatrix
import Q1Paper.PaperI.S03_Certificate.GramSystem
import Q1Paper.PaperI.S03_Certificate.Claim11_Window
import Q1Paper.PaperI.S03_Certificate.MinorRank
import Q1Paper.PaperI.S03_Certificate.SpectralMinor
import Q1Paper.PaperI.S08_ChartEquivalence.Complexify
import Q1Paper.PaperI.S03_Certificate.Claim11_MinorsGram
import Q1Paper.PaperI.S03_Certificate.Claim12
import Q1Paper.PaperI.S03_Certificate.CauchyBinet
import Q1Paper.PaperI.S03_Certificate.GramKernel
import Q1Paper.PaperI.S03_Certificate.GramCoefficients
import Q1Paper.PaperI.S03_Certificate.GramCompression
import Q1Paper.PaperI.S03_Certificate.MinorFamilyBridge
import Q1Paper.PaperI.S03_Certificate.FibreSum
import Q1Paper.PaperI.S03_Certificate.FibreCard
import Q1Paper.PaperI.S03_Certificate.WindowSign
import Q1Paper.PaperI.S03_Certificate.GramFamilyBridge
import Q1Paper.PaperI.S03_Certificate.GramSubspace
import Q1Paper.PaperI.S03_Certificate.RowSpanBridge
import Q1Paper.PaperI.S04_Rationality.BitLen
import Q1Paper.PaperI.S04_Rationality.BitLenAdd
import Q1Paper.PaperI.S04_Rationality.InputLen
import Q1Paper.PaperI.S05_Complexity.BareissBase
import Q1Paper.PaperI.S05_Complexity.DesnanotJacobi
import Q1Paper.PaperI.S05_Complexity.BareissTableau
import Q1Paper.PaperI.S05_Complexity.BareissAssemble
import Q1Paper.PaperI.S04_Rationality.Claim16
import Q1Paper.PaperI.S03_Certificate.Claim16_Gcd
import Q1Paper.PaperI.S02_Subspace.Claims38
import Q1Paper.PaperI.S07_ExistsReal.Theorem5
import Q1Paper.PaperI.S02_Subspace.RankFactorization
import Q1Paper.PaperI.S04_Rationality.RationalBasis
import Q1Paper.PaperI.S04_Rationality.Claim15_Arithmetic
import Q1Paper.PaperI.S04_Rationality.MinorCoeff
import Q1Paper.PaperI.S04_Rationality.Claim15
import Q1Paper.PaperI.S02_Subspace.Claim14
import Q1Paper.PaperI.S07_ExistsReal.T5Complete
import Q1Paper.PaperI.S07_ExistsReal.T5DecC
import Q1Paper.PaperI.S07_ExistsReal.T5Auto
import Q1Paper.PaperI.S05_Complexity.CostCore
import Q1Paper.PaperI.S02_Subspace.SolveCriterion
import Q1Paper.PaperI.S05_Complexity.Hadamard
import Q1Paper.PaperI.S05_Complexity.CostBareiss
import Q1Paper.PaperI.S05_Complexity.ComplexityCounts
import Q1Paper.PaperI.S04_Rationality.BitLenMatMul
import Q1Paper.PaperI.S04_Rationality.RatDescent
import Q1Paper.PaperI.S02_Subspace.Claim14_Bases
import Q1Paper.PaperI.S01_Compression.KernelBasis
import Q1Paper.PaperI.S03_Certificate.BezoutBounded
import Q1Paper.PaperI.S06_Algorithms.ChartCount
import Q1Paper.PaperI.S04_Rationality.TauMConst
import Q1Paper.PaperI.S04_Rationality.ColsConcat
import Q1Paper.PaperI.S05_Complexity.TotalCost
import Q1Paper.PaperI.S05_Complexity.ExactDiv
import Q1Paper.PaperI.S06_Algorithms.Thm1Cond
import Q1Paper.PaperI.S06_Algorithms.Thm1Bite
import Q1Paper.PaperI.S06_Algorithms.RenegarParams
import Q1Paper.PaperI.S06_Algorithms.FptCore
import Q1Paper.PaperI.S02_Subspace.Claim4Converse
import Q1Paper.PaperI.S06_Algorithms.FptSpec
import Q1Paper.PaperI.S06_Algorithms.Prop4
import Q1Paper.PaperI.S03_Certificate.GramBitLength
import Q1Paper.PaperI.S03_Certificate.CompressedGram
import Q1Paper.PaperI.S06_Algorithms.DecR0Iface
import Q1Paper.PaperI.S04_Rationality.DenOne
import Q1Paper.PaperI.S06_Algorithms.FinReindex
import Q1Paper.PaperI.S02_Subspace.Claim8_SumSquares
import Q1Paper.PaperI.S02_Subspace.Claim8_Disjunction
import Q1Paper.PaperI.S02_Subspace.Claim8_ElemSymm
import Q1Paper.PaperI.S08_ChartEquivalence.ChartComplete
import Q1Paper.PaperI.S08_ChartEquivalence.FromRowsMap
import Q1Paper.PaperI.S08_ChartEquivalence.ChartComplex
import Q1Paper.PaperI.S08_ChartEquivalence.ReindexAlgebraic
import Q1Paper.PaperI.S08_ChartEquivalence.ReindexSpectral
import Q1Paper.PaperI.S08_ChartEquivalence.Soundness
import Q1Paper.PaperI.S08_ChartEquivalence.DecComplex
import Q1Paper.PaperI.S08_ChartEquivalence.KernelLift
import Q1Paper.PaperI.S08_ChartEquivalence.ComplexSoundness
import Q1Paper.PaperI.S08_ChartEquivalence.ComplexCompression
import Q1Paper.PaperI.S08_ChartEquivalence.ComplexCompleteness
/-!
Q1Paper/PaperI/MainTheorems.lean

Paper I entry point: it imports exactly the modules that belong to Paper I
(feasibility, compression, finite certificate, fixed-order and FPT upper
bounds) and nothing from the companion papers (minimum order, hyperplane layer,
c2 layer).

The imported modules are the formalized material; the paper-level statements
and their status are recorded in `docs/PAPER_I_PROOF_MAP.md` and `docs/START_HERE.md`.  This
file is an index, not a proof: the theorems live in the modules imported below,
under the namespaces `Q1Paper`, `Q1Subspace` and `KappaObs`.
-/


/-!
## What is imported here

* compression / rank identity: `Basic`, `RankIdentity`, `G4RankIdentity`,
  `Compression`, `Q1Compression`;
* row spaces and subspaces: `Q1RankInclusion`, `Q1RowSpace`, `Q1Subspace`,
  `KappaObs`, `FreeRows`, `Q1Projection`, `Q1Pencil`, `Q1Step3`, `BoundLower`;
* monotonicity: `Monotone`, `MonotoneBlocks`;
* the certificate: `RankConsistency`, `G5GramRank`, `BezoutDeg`, `BezoutReal`,
  `SpectralCertificate`, `Window`;
* the zero-free-row algebra: `G3Adjugate`, `G3LeftInverse`, `G3Coeff`,
  `DegreeBounds`;
* the algorithms' algebraic interfaces: `FixedOrder`, `FPT`;
* the statement layer: `PaperI.Interface`;
* the matrix-level Claim 2: `PaperI.CompressionMatrix`
  (`rawAlgebraic_iff_compressed`, `rawSpectral_iff_compressed`,
  `rawAlgebraic_iff_rowSpace`, `DEC_iff_compressed`).

## What is *not* imported

`MinOrder`, `TightDim` (Paper II), `Strata`, `FullRank`, `HyperplaneAvoid`,
`HyperplaneDirection`, `HyperplanePrescribed`, `HyperplaneFibre` (Paper III).
-/
