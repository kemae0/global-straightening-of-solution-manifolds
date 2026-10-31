# Checked dependency map

This table replaces the earlier incomplete audit. Every existence theorem
listed here is derived from its stated analytic hypotheses.

| Dependency or manuscript result | Checked modules / theorem |
| --- | --- |
| Genuine complete normed C¹ histories and classical correspondence | `HistorySpace` |
| Endpoint and derivative evaluation, continuous inclusion | `HistorySpace`, `ScalarHistoryLift` |
| Actual terminal corrections, support and small continuous norm | `BoundaryLayer`, `BoundaryScaling` |
| Scalar and matrix Riesz representation | `PositiveFunctionalDecomposition`, `ScalarRieszRepresentation`, `HistoryFunctionalRepresentation`, `VectorRieszRepresentation` |
| Endpoint-atom limit and zero-atom characterization | `TerminalAtomLimit`, `HistoryTerminalAtom`, `MatrixTerminalAtom`, `AtomFreeRepresentation` |
| Separable derivative image and a common finite reference/dominator | `HistorySeparable`, `IntervalReferenceMeasure`, `CommonDominatingMeasure` |
| Positive finite-rank Markov approximants | `WeightedAverages`, `SmallSupportPartitions`, `MarkovApproximation` |
| Adjoint approximation of integrable densities and dominated measures | `IntegralDensityFunctional`, `SelfAdjointApproximation`, `MarkovAdjoint` |
| Actual terminal cutoff and its adjoint limit | `TerminalHistoryCutoff`, `TerminalCutoffAdjoint` |
| Reconstructed R_m: finite rank, uniform bounds, strong limit and annihilation | `ReconstructedApproximants`, `AdaptedHistoryOperators` |
| Matrix adjoint convergence and extension from the dense family | `MatrixAdaptedAdjoint`, `DenseDualApproximation`, `SeparableAdaptedOperators` |
| Bounded finite-dimensional cylindrical approximants | `FiniteCutoff`, `CylindricalPieces`, `UniformCylindricalFamily` |
| Local C¹ approximation in operator norm | `ApproximationLimits`, `LocalC1Approximation`, `UniformLocalC1Approximation` |
| Shell overlap, local uniform function/derivative convergence | `ShellGeometry`, `TerminalShells`, `VanishingSeries`, `C1LinearSeries`, `TerminalShellSeries` |
| Exact coordinate and endpoint defect | `ShellCoordinate` |
| Finite filtration and nilpotence | `FiniteFiltration`, `FiniteTriangular` |
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
| Genuine Hilbert cutoffs near closed sets | `HilbertBumps`, `HilbertPositiveSupport`, `HilbertCutoff` |
| Bounded C¹ Hilbert output saturation and extension | `HilbertSaturation`, `HilbertBoundedExtension` |
| Hilbert observation spaces and actual Bernstein reconstruction | `HilbertHistoryObservations` |
| Hilbert cylindrical local C¹ approximation | `HilbertCylindricalFamily` |
| Full separable Hilbert theorem, including spectrum and isotopy | `HilbertNormalizedExistence`, `HilbertExistence.property_e_Hilbert_full_straightening` |

The measure representation is expressed using finite positive-measure
pairs. Adjoint convergence extends directly by operator-norm closure; the
written proof's separate assertions of total-variation continuity and
absolute continuity of every representing measure in the full image are
not separately certified, and are not used as assumptions in these proofs.

The coordinate construction uses a precise quantitative terminal-invisibility
hypothesis. The actual finite-state and Hilbert observations satisfy it.
Nestedness of observation grids is unnecessary in the checked induction.

All degenerate-case corrections are explicit in
`MANUSCRIPT_CORRECTIONS.md`. No version of an uncorrected false spectrum
or impossibility statement is asserted as a theorem.
