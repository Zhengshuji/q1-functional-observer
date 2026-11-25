
import Q1Paper.Basic
import Q1Paper.RankIdentity
import Q1Paper.G4RankIdentity
import Q1Paper.Compression
import Q1Paper.Q1Compression
import Q1Paper.Q1RankInclusion
import Q1Paper.Q1RowSpace
import Q1Paper.Q1Subspace
import Q1Paper.KappaObs
import Q1Paper.FreeRows
import Q1Paper.Q1Projection
import Q1Paper.Q1Pencil
import Q1Paper.Q1Step3
import Q1Paper.BoundLower
import Q1Paper.Monotone
import Q1Paper.MonotoneBlocks
import Q1Paper.RankConsistency
import Q1Paper.G5GramRank
import Q1Paper.BezoutDeg
import Q1Paper.BezoutReal
import Q1Paper.SpectralCertificate
import Q1Paper.Window
import Q1Paper.G3Adjugate
import Q1Paper.G3LeftInverse
import Q1Paper.G3Coeff
import Q1Paper.DegreeBounds
import Q1Paper.FixedOrder
import Q1Paper.FPT
import Q1Paper.PaperI.Interface
import Q1Paper.PaperI.CompressionMatrix
import Q1Paper.PaperI.GramSystem
import Q1Paper.PaperI.Claim11_Window
import Q1Paper.PaperI.MinorRank
import Q1Paper.PaperI.SpectralMinor
import Q1Paper.PaperI.Complexify
import Q1Paper.PaperI.Claim11_MinorsGram
import Q1Paper.PaperI.Claim12
import Q1Paper.PaperI.CauchyBinet
import Q1Paper.PaperI.GramKernel
import Q1Paper.PaperI.GramCoefficients
import Q1Paper.PaperI.GramCompression
import Q1Paper.PaperI.MinorFamilyBridge
import Q1Paper.PaperI.FibreSum
import Q1Paper.PaperI.FibreCard
import Q1Paper.PaperI.WindowSign
import Q1Paper.PaperI.GramFamilyBridge
import Q1Paper.PaperI.GramSubspace
import Q1Paper.PaperI.RowSpanBridge
import Q1Paper.PaperI.BitLen
import Q1Paper.PaperI.BitLenAdd
import Q1Paper.PaperI.InputLen
import Q1Paper.PaperI.BareissBase
import Q1Paper.PaperI.DesnanotJacobi
import Q1Paper.PaperI.BareissTableau
import Q1Paper.PaperI.BareissAssemble
import Q1Paper.PaperI.Claim16
import Q1Paper.PaperI.C16Gcd
import Q1Paper.PaperI.Claims38
import Q1Paper.PaperI.Theorem5
import Q1Paper.PaperI.RankFactorization
import Q1Paper.PaperI.RationalBasis
import Q1Paper.PaperI.Claim15iv
import Q1Paper.PaperI.MinorCoeff
import Q1Paper.PaperI.Claim15
import Q1Paper.PaperI.Claim14
import Q1Paper.PaperI.T5Complete
import Q1Paper.PaperI.T5DecC
import Q1Paper.PaperI.T5Auto
import Q1Paper.PaperI.CostCore
import Q1Paper.PaperI.SolveCriterion
import Q1Paper.PaperI.Hadamard
import Q1Paper.PaperI.CostBareiss
import Q1Paper.PaperI.ComplexityCounts
import Q1Paper.PaperI.BitLenMatMul
import Q1Paper.PaperI.RatDescent
import Q1Paper.PaperI.Claim14Basis
import Q1Paper.PaperI.KernelBasis
import Q1Paper.PaperI.BezoutBounded
import Q1Paper.PaperI.ChartCount
import Q1Paper.PaperI.TauMConst
import Q1Paper.PaperI.ColsConcat
import Q1Paper.PaperI.TotalCost
import Q1Paper.PaperI.ExactDiv
import Q1Paper.PaperI.Thm1Cond
import Q1Paper.PaperI.Thm1Bite
import Q1Paper.PaperI.RenegarParams
import Q1Paper.PaperI.FptCore
import Q1Paper.PaperI.Claim4Converse
import Q1Paper.PaperI.FptSpec
import Q1Paper.PaperI.Prop4
import Q1Paper.PaperI.GramBitLength
import Q1Paper.PaperI.CompressedGram
import Q1Paper.PaperI.DecR0Iface
import Q1Paper.PaperI.DenOne
import Q1Paper.PaperI.FinReindex
import Q1Paper.PaperI.Claim8_SumSquares
import Q1Paper.PaperI.Claim8_Disjunction
import Q1Paper.PaperI.Claim8_ElemSymm
import Q1Paper.PaperI.ChartComplete
import Q1Paper.PaperI.FromRowsMap
import Q1Paper.PaperI.ChartComplex
import Q1Paper.PaperI.ReindexAlgebraic
import Q1Paper.PaperI.ReindexSpectral
import Q1Paper.PaperI.Soundness
import Q1Paper.PaperI.DecComplex
import Q1Paper.PaperI.KernelLift
import Q1Paper.PaperI.ComplexSoundness
import Q1Paper.PaperI.ComplexCompression
import Q1Paper.PaperI.ComplexCompleteness
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
