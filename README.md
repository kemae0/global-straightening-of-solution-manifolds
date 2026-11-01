# Global Straightening of Solution Manifolds for State-Dependent Delay Equations

Lean 4 proofs accompanying Lily DiPaulo's research manuscript of October 31, 2026.

The library constructs an ambient C¹ diffeomorphism on an arbitrary open
history domain under property (e). In finite dimensions it also proves
existence under the weaker zero-terminal-atom condition. The chart satisfies

$$
(A\phi)'(0)=\phi'(0)-f(\phi),\qquad
A(X_f)=A(U)\cap X_0.
$$

It preserves the value at zero, fixes the history on any prescribed
`[-h, -τ]`, and has an arbitrarily small common displacement bound in the
continuous-history norm. The finite-state and nonzero separable Hilbert
results include derivative spectrum `{1}` and the affine C¹ isotopy
`A_s = id + s(A - id)`.

## Alignment with the current paper

- [Supplied manuscript](manuscript/paper_revised.tex): the latest attachment,
  preserved byte for byte, including the expanded introduction and bibliography.
- [Certificate source](manuscript/paper_corrected.tex): an identical copy of
  the latest supplied text, retained at this path for the verification scripts.
- [Claim map](verification/manuscript-coverage.json): source locations and
  Lean declarations for the results and construction claims under review.
- [Formalization audit](FORMALIZATION_AUDIT.md) and
  [dependency map](PROOF_OBLIGATIONS.md): precise representations and scope.

The paper's sum norm `‖φ‖₁ = ‖φ‖ + ‖φ′‖` is implemented on
`SumC1History`, a complete closed graph satisfying the fundamental theorem
of calculus. `sumHistoryEquiv` gives a continuous linear equivalence with
the earlier maximum-norm model. The principal sum-norm theorem allows
arbitrary finite-dimensional real state norms. Bernstein contraction and
the stated convergence estimates are also proved in the sum norm.

The chart certificates include a strictly positive common displacement
constant below epsilon for every affine slice with parameter in `[0,1]`.
The local C¹ approximation is in operator norm; the literal strict local
supremum estimate is proved separately.

## Reflection example: wording resolved

The latest manuscript distinguishes all conclusions of Theorem 3.3
(`thm:no-atom`) from existence of a C¹ diffeomorphism satisfying the defect
identity. This resolves the overbroad wording in the preceding draft and
matches the Lean reflection result.

For endpoint differentiation `D` and a bounded right inverse `Q`, the map
`A = I - 2QD` is an ambient linear involution satisfying `DA = -D`.
For nonzero `a`, however, `A(Qa) = -Qa`, so its derivative has eigenvalue
`-1`. It cannot satisfy the theorem's spectrum conclusion `{1}`.
`EndpointReflection.lean` proves the involution, the defect identity and
the spectral obstruction. In fact the obstruction applies to every C¹
chart with the same defect identity on a nonempty open domain.

The example proves that the zero-atom condition is not necessary for
ambient defect straightening. It does not assert all the theorem's further
conclusions. See [MANUSCRIPT_CORRECTIONS.md](MANUSCRIPT_CORRECTIONS.md) for
the resolved issue and the historical corrections already incorporated
into the current draft. The supplied manuscript has not been edited.

## Main Lean certificates

All names below belong to the `GlobalRegularization` namespace.

| Paper result | Lean certificate |
| --- | --- |
| Principal theorem, spectrum, localized isotopy and shared positive bound | `property_e_revised_main` |
| Principal theorem on the exact sum-norm model, arbitrary finite-dimensional state norm | `property_e_sum_finite_dimensional` |
| Zero-terminal-atom theorem on the sum-norm model | `terminal_atom_sum_finite_main` |
| Nonzero separable Hilbert-valued theorem on the sum-norm model | `property_e_sum_Hilbert_main` |
| Actual signed-measure representation and one-sided terminal-atom limit | `historyFunctional_signed_matrix_representation`, `matrixHistoryFunctional_terminal_filter_limit` |
| Full-image dominating measure and adapted operators | `exists_full_image_totalVariation_dominator`, `exists_adapted_operators_for_separable_family` |
| Level sets, global split fiber parametrizations, tangent kernels and complementary planes | `terminal_atom_fiber_geometry`, `C1Straightening.fiberTangent_range` |
| Invertible endpoint coupling | `terminal_atom_endpoint_coupling_of_isUnit` |
| Remote observations with arbitrary Banach observation range | `remote_observation_full_straightening` |
| Past-derivative example and failure of property (e) on domains containing zero | `pastDerivative_full_straightening`, `scalarPastDerivativeFeedback_not_property_e_on_zero_domain` |

For a zero state space the spatial conclusions remain available, while
the spectrum is empty; separate theorems use spectrum inclusion. Empty
open domains are included. Infinite-dimensional Hilbert cutoffs are
constructed without assuming compactness of bounded balls.

## Reproduce the checks

The project pins Lean **4.24.0** and mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (`v4.24.0`).

```text
lake exe cache get
lake build
lake env lean scripts/Audit.lean
lake env lean scripts/MainCertificate.lean
lake env lean scripts/PaperCertificate.lean
lake env lean scripts/ManuscriptCoverage.lean
lake env lean scripts/RevisionCertificate.lean
```

On Windows, `scripts/Lean.ps1` runs these commands using a local Lean
distribution when available. GitHub Actions repeats the build and checks.
Verification logs, input hashes and the source manifest are in `verification/`.
Compiler binaries, dependency checkouts and the original unchecked archive
are excluded from the published sources.

`Audit.lean` traverses the transitive axiom dependencies of every declaration
in the project namespace. It permits only `propext`, `Classical.choice` and
`Quot.sound`, rejecting `sorryAx` and additional mathematical axioms.

## What these checks establish

Lean checks the formal statements and their proofs from their stated
hypotheses. The coverage checker verifies source anchors and declaration
references. Matching prose to those declarations remains a manual
mathematical audit; the checker does not establish that every sentence of
the manuscript is formalized or that the paper is free of all errors.

Cited semiflow theory, historical and priority claims, and the applicability
to hypotheses in external papers remain background. The bibliography is
not a Lean certificate. Split-submanifold conclusions are expressed through
explicit C¹ kernel charts, tangent maps and continuous complements.

The original input versions remain preserved locally, with their hashes
and the current source hashes in `verification/provenance.json`.
See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for the mathlib proof
adaptation notices and `LICENSE.mathlib` for its license.
