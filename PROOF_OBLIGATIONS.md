# Checked dependency map

This table replaces the earlier incomplete audit. Every existence theorem
listed here is derived from its stated analytic hypotheses.

| Dependency or manuscript result | Checked modules / theorem |
| --- | --- |
| Genuine complete normed C¹ histories and classical correspondence | `HistorySpace` |
| Endpoint and derivative evaluation, continuous inclusion | `HistorySpace`, `ScalarHistoryLift` |
| Actual terminal corrections, support and small continuous norm | `BoundaryLayer`, `BoundaryScaling` |
| Scalar and matrix Riesz representation | `PositiveFunctionalDecomposition`, `ScalarRieszRepresentation`, `HistoryFunctionalRepresentation`, `VectorRieszRepresentation` |
| Actual signed matrix representation, uniqueness and total-variation duality | `SignedMeasureDuality`, `FullImageDomination` |
| Total-variation continuity, closedness of absolute continuity and full-image domination | `SignedMeasureDuality`, `FullImageDomination.exists_full_image_totalVariation_dominator` |
| Endpoint-atom limit and zero-atom characterization | `TerminalAtomLimit`, `HistoryTerminalAtom`, `MatrixTerminalAtom`, `AtomFreeRepresentation` |
| Separable derivative image and a common finite reference/dominator | `HistorySeparable`, `IntervalReferenceMeasure`, `CommonDominatingMeasure` |
| Positive finite-rank Markov approximants | `WeightedAverages`, `SmallSupportPartitions`, `MarkovApproximation` |
| Adjoint approximation of integrable densities and dominated measures | `IntegralDensityFunctional`, `SelfAdjointApproximation`, `MarkovAdjoint` |
| Explicit signed adjoint density and actual total-variation estimates | `SignedMeasureAdjoints` |
| Actual terminal cutoff and its adjoint limit | `TerminalHistoryCutoff`, `TerminalCutoffAdjoint` |
| Reconstructed R_m: finite rank, uniform bounds, strong limit and annihilation | `ReconstructedApproximants`, `AdaptedHistoryOperators` |
| Matrix adjoint convergence and extension from the dense family | `MatrixAdaptedAdjoint`, `DenseDualApproximation`, `SeparableAdaptedOperators` |
| Bounded finite-dimensional cylindrical approximants | `FiniteCutoff`, `CylindricalPieces`, `UniformCylindricalFamily` |
| Local C¹ approximation in operator norm | `ApproximationLimits`, `LocalC1Approximation`, `UniformLocalC1Approximation` |
| Shell overlap, local uniform function/derivative convergence | `ShellGeometry`, `TerminalShells`, `VanishingSeries`, `C1LinearSeries`, `TerminalShellSeries` |
| Exact coordinate and endpoint defect | `ShellCoordinate` |
| Finite filtration and nilpotence | `FiniteFiltration`, `FiniteTriangular` |
| Written one-sided power expansion | `OneSidedPower` |
| K_N R_N = 0 and norm-small remainder | `TriangularLimit`, `ShellTelescoping`, `ShellInvertibility` |
| Genuine complexification and actual derivative spectrum | `RealComplexification`, `ComplexificationModel`, `ComplexifiedSpectrum`, `TriangularDerivative` |
| Global injectivity for varying observation spaces | `Triangular`, `GeneralShellObservations` |
| Banach inverse theorem and C¹ inverse on open image | `GlobalInverse` |
| Uniform displacement, support, endpoint preservation | `ShellDisplacement`, `ApproximantStraightening` |
| Affine isotopy and localized slices | `TriangularHomotopy`, `ShellIsotopy`, `GeneralShellObservations`, `LocalizedIsotopy` |
| General positive history length | `HistoryRescale`, `HistoryRescaleEquiv`, `LocalizedTransport`, `TriangularDerivativeConjugate` |
| Principal finite-state theorem | `MainExistence.mainClaim` |
| Stronger finite-state theorem with spectrum | `TerminalExistence`, `FiniteFullTheorem.terminal_atom_full_straightening` |
| All-level and solution-manifold identities | `C1Specification`, `PrincipalApplications`, `TerminalApplications`, `FiberApplications` |
| Split fiber charts, tangent kernels, continuous normal planes, codimension | `SplitFibers`, `FiberTangents` |
| Invertible endpoint-derivative coupling | `EndpointLinearEquiv`, `EndpointCoupling`, `TerminalApplications` |
| Remote-observation theorem with spectrum | `RemoteTerminalCondition.remote_observation_full_straightening` |
| Past-derivative example and failure of derivative extension | `PastDerivativeApplication`, `PastDerivativeNonextension` |
| Corrected endpoint-identity obstruction and counterexamples | `EndpointObstruction`, `Counterexamples` |
| Infinitely smooth Hilbert cutoffs and partitions of unity | `HilbertSmoothBounds`, `HilbertSmoothSupport`, `HilbertCutoff`, `HilbertSmoothPartitions` |
| Bounded C¹ Hilbert output saturation and extension | `HilbertSaturation`, `HilbertBoundedExtension` |
| Hilbert observation spaces and actual Bernstein reconstruction | `HilbertHistoryObservations` |
| Hilbert cylindrical local C¹ approximation | `HilbertCylindricalFamily` |
| Exact degree-4^m operators, nested grids and terminal invisibility | `PaperBernsteinGrids` |
| Actual Bernstein ranges and equivalent finite Hilbert product norms | `FiniteTensorCoefficients`, `BernsteinRealIndependence`, `BernsteinHistoryRanges` |
| Smooth cutoffs on the actual ranges | `BernsteinRangeCutoffs` |
| Displayed closed distance cores, open belts and saturation formula | `ManuscriptCutoffs` |
| The displayed cutoff/saturation family used in the Hilbert proof | `ManuscriptHilbertFamily` |
| Joint-action local operator bounds and literal supremum displacement | `ManuscriptDetails` |
| Endpoint atom hypothesis is sufficient but not necessary | `ManuscriptDetails.twiceEndpoint_not_terminal`, `twiceEndpointStraightening` |
| Full separable Hilbert theorem, including spectrum and isotopy | `HilbertNormalizedExistence`, `HilbertExistence.property_e_Hilbert_full_straightening` |

The signed measure representation uses mathlib's actual signed measures;
their integrals are differences of integrals against the Jordan parts.
Total-variation continuity and full-image absolute continuity are now
separately certified and used in the terminal existence construction.

The coordinate construction uses a precise quantitative terminal-invisibility
hypothesis. The actual finite-state and Hilbert observations satisfy it.
Nestedness is unnecessary in the general induction, but is also proved
directly for the manuscript's degree-4^m operators. The Hilbert existence
proof uses those operators and the displayed range cutoff/saturation family.

The source-anchored assertion map is `verification/manuscript-coverage.json`.
`scripts/ManuscriptCoverage.lean` checks every theorem reference and anchor.

All degenerate-case corrections are explicit in
`MANUSCRIPT_CORRECTIONS.md`. No version of an uncorrected false spectrum
or impossibility statement is asserted as a theorem.
`LiteralManuscriptObstructions` proves a counterexample to the written
Hilbert conclusion with its actual history-space hypotheses satisfied.
