/-
Q1Paper/PaperI/MainTheorems.lean

Paper I entry point: it imports exactly the modules that belong to Paper I
(feasibility, compression, finite certificate, fixed-order and FPT upper
bounds) and nothing from the companion papers (minimum order, hyperplane layer,
c2 layer).

The imported modules are the formalized material; the paper-level statements
and their status are recorded in `paper/PAPER_I_FORMALIZATION_MAP.md`.  This
file is an index, not a proof: the theorems live in the modules imported below,
under the namespaces `Q1Paper`, `Q1Subspace` and `KappaObs`.
-/

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
import Q1Paper.PaperI.Gram
import Q1Paper.PaperI.Claim11
import Q1Paper.PaperI.MinorRank
import Q1Paper.PaperI.SpectralMinor
import Q1Paper.PaperI.Complexify
import Q1Paper.PaperI.Claim11Final
import Q1Paper.PaperI.Claim12
import Q1Paper.PaperI.CauchyBinet
import Q1Paper.PaperI.GramKernel
import Q1Paper.PaperI.GramCoefficients
import Q1Paper.PaperI.GramCompression
import Q1Paper.PaperI.MinorFamilyBridge
import Q1Paper.PaperI.FibreSum
import Q1Paper.PaperI.BitLen
import Q1Paper.PaperI.BitLenAdd

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
