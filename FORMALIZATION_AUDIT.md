# Formalization audit — October 31, 2026

The final supplied paper is preserved exactly in
`manuscript/global_straightening_solution_manifolds.tex`. The certificate
target `manuscript/paper_corrected.tex` and compatibility copy
`manuscript/paper_revised.tex` are byte-identical to that supplied file.
The author corrected the endpoint-reflection comparison: the example gives
an ambient defect straightening, without asserting the full no-atom
theorem's spectrum `{1}`. `EndpointReflection` proves the exact involution,
defect identity and spectral distinction. See
[MANUSCRIPT_CORRECTIONS.md](MANUSCRIPT_CORRECTIONS.md).

The older false zero-space spectral assertion is repaired in the revised
draft; its counterexample remains checked in the library. Both current
source hashes and the earlier manuscript provenance are recorded.

## What is proved

`mainClaim` proves the principal property-(e) existence theorem on the genuine
Banach space `C1History h (Fin n → ℝ)` for every positive history length and
arbitrary open domain. It constructs an ambient C¹ chart with a C¹ inverse
on its open image, the exact compatibility-defect identity, preservation of
endpoint value and remote history, and a common continuous-history norm
bound strictly below the requested epsilon.

`terminal_atom_full_straightening` proves the stronger terminal-atom theorem.
Its hypothesis is the sequential form of the positive-width terminal limit;
`historyFunctional_terminal_sequences_iff` and `MatrixTerminalAtom` establish
the equivalence with the endpoint-atom condition. It includes the affine
isotopy and spectrum `{1}` for the actual complexified derivative in positive
state dimension. Spectrum inclusion is proved without that restriction.

`property_e_Hilbert_full_straightening` proves the corresponding result for
any nontrivial separable real Hilbert space, with no finite-dimensionality
hypothesis. A separate inclusion theorem includes the zero Hilbert space.
The Hilbert cutoffs and partitions of unity are now proved infinitely smooth,
using direct bounds for every radial-bump derivative on bounded balls.
The bounded saturation, cylindrical approximants, strong
operator approximation, local C¹ operator-norm approximation, shell series,
global injectivity, inverse and time transport are all constructed and proved.

The application modules prove all-level identities, global C¹ fiber
parametrizations by open subsets of the split kernel, the tangent-kernel
identity, a continuous family of complementary planes of dimension n,
codimension n, invertible endpoint coupling, remote observations with arbitrary
Banach observation ranges, and the concrete past-derivative example. The
failure of property (e) for the scalar example at the zero history is proved.

The affine slices are C¹ diffeomorphisms for every real parameter. For
parameters in `[0,1]`, `LocalizedIsotopy` also proves preservation of the
localization and common strict displacement bound.

## Genuine models and proof dependencies

The revision explicitly chooses the sum history norm. `SumHistoryNorm`
constructs the genuine closed FTC graph with norm `‖φ‖ + ‖φ′‖`, proves it
complete, and constructs the continuous linear equivalence with the older
maximum-norm graph, with constants 1 and 2. `CoordinateTransport` transports
the chart and its actual affine isotopy. `SumHistoryCertificates` derives
finite-state, terminal-defect and Hilbert existence theorems on this sum-norm
space. The finite-dimensional property-(e) theorem allows an arbitrary real
state norm. `SumBernstein` separately proves the exact contraction constant
1, strong limit, continuous-history operator-norm limit and nestedness in
the sum model.

`RevisedMainTheorems` includes the principal theorem's newly stated spectrum,
solution-set image identity, localized affine isotopy and a single strictly
positive displacement constant below epsilon for every slice in `[0,1]`.
`RevisedAssertions` proves the literal strict local supremum estimate and
failure of property (e) for the past-derivative example on every domain
containing zero. The general coordinate theorem already permits separating
observations without a nestedness hypothesis, as in the revised lemma.

Histories are continuous value/derivative pairs constrained by the fundamental
theorem of calculus. This closed graph is complete, corresponds to classical
C¹ histories for positive history length, and carries the actual evaluation,
derivative-evaluation and continuous-history inclusion maps.

The complexification is the space of real continuous linear maps from ℂ
with scalar action by precomposition. Its real embedding is isometric, every
element is `x + i y`, and extension of a real operator is unique. The actual
coordinate derivative is extended through this construction before its
spectrum is calculated.

Finite-state Riesz representations now include actual `SignedMeasure`
matrices, with their integrals defined through the Jordan positive/negative
parts. Uniqueness is proved. `signedVariationNorm` is the real mass of
mathlib's actual `SignedMeasure.totalVariation`; its equality with the
continuous-functional norm is a theorem, not the definition.
Total-variation continuity and closure of absolute continuity under such
limits are proved. A common finite dominator covers every component in the
full separable derivative image, retains full support and has zero endpoint
atom. The terminal existence proof now uses this full-image measure route.
The signed Markov adjoint density, contraction and total-variation limits,
and the explicit two-times-terminal-tail bound are checked separately.
`TerminalFilterLimit` proves the actual positive-real-width one-sided limit.
`OneSidedPower` proves the written noncommutative finite power formula.

Global fiber charts and tangent maps are explicit. This avoids depending on
a general submanifold API: the formal certificate contains the open kernel
parameter domains, C¹ maps, inverse identities, tangent range and codimension.

No main existence conclusion is introduced as an axiom or supplied as an
additional hypothesis. No `sorry` or `admit` is accepted. Classical choice and
the standard logical axioms used by mathlib are allowed.

## Verification

The project pins Lean 4.24.0 and mathlib
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

Run `lake build`, then `scripts/Audit.lean`, `scripts/MainCertificate.lean`,
`scripts/PaperCertificate.lean`, `scripts/ManuscriptCoverage.lean`, and
`scripts/RevisionCertificate.lean` through `lake env lean`. The audit covers
every declaration in the project namespace, including helper definitions
and counterexamples, and allows only `propext`, `Classical.choice`, and
`Quot.sound`. Exact outputs and a source manifest are stored in `verification/`.

The original tooling limitation has been resolved locally: the official Lean
4.24.0 distribution and matching mathlib are installed in this workspace.
The unrelated parent Git repository was not modified. The original ZIP is
preserved separately and is not imported into the checked library.

`scripts/ManuscriptCoverage.lean` validates the source-anchored claim map
and checks that each proof reference names a theorem in the built environment.
This is a correspondence audit, not a proof that prose and Lean are equivalent.
The theorem-coverage script concerns the supplied manuscript's own new
mathematical results. Bibliographic assertions and external cited results
are not certified. See README and the dependency map for the exact formal
counterparts and proof-route differences.

## Corrected construction coverage

The earlier unrestricted spectrum and impossibility assertions have
counterexamples, not proofs. The earlier input and current supplied input
are preserved. The latest reflection comparison includes the author's
explicit qualification; there are no agent edits to the current source.
The displayed degree-4^m Bernstein construction is now checked, including
continuous linear equivalence of its actual closed ranges with finite Hilbert
products and nestedness stated directly for P_m. The Hilbert existence proof
uses these observations and the manuscript's actual cutoff/saturation formula.
The displayed distance cores and open belts, smooth range cutoffs, local
operator bounds for extended derivatives, literal supremum estimate, and the
non-necessity example are separately certified. Normalizing the interval to
[-1,0], transporting back, and reindexing positive indices preserve the stated
claims. The coverage map records formal counterparts; prose, bibliographic
claims and the external semiflow theory are not assertions proved here.
