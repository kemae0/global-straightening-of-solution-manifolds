# Formalization audit — October 31, 2026

The manuscript's new existence theorems and application corollaries now have
kernel-checked Lean counterparts, with the explicit corrections listed in
[MANUSCRIPT_CORRECTIONS.md](MANUSCRIPT_CORRECTIONS.md). The original prose
article, including its uncorrected degenerate cases, is not certified verbatim.

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
The Hilbert cutoffs, bounded saturation, cylindrical approximants, strong
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

Histories are continuous value/derivative pairs constrained by the fundamental
theorem of calculus. This closed graph is complete, corresponds to classical
C¹ histories for positive history length, and carries the actual evaluation,
derivative-evaluation and continuous-history inclusion maps.

The complexification is the space of real continuous linear maps from ℂ
with scalar action by precomposition. Its real embedding is isometric, every
element is `x + i y`, and extension of a real operator is unique. The actual
coordinate derivative is extended through this construction before its
spectrum is calculated.

Finite-state Riesz representations use differences of finite positive Borel
measures. Endpoint atoms and their operator-norm limit are proved for these
representations. The common finite dominator is constructed for a countable
dense subfamily, retaining full support and zero endpoint atom. Uniform
operator bounds extend the resulting adjoint approximation to the whole
separable derivative image directly in operator norm. Thus the existence
proof does not assume the manuscript's separate total-variation continuity
or full-image domination claims. Those intermediate claims are not separately
formalized by this development.

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
and `scripts/PaperCertificate.lean` through `lake env lean`. The audit covers
every declaration in the project namespace, including helper definitions
and counterexamples, and allows only `propext`, `Classical.choice`, and
`Quot.sound`. Exact outputs and a source manifest are stored in `verification/`.

The original tooling limitation has been resolved locally: the official Lean
4.24.0 distribution and matching mathlib are installed in this workspace.
The unrelated parent Git repository was not modified. The original ZIP is
preserved separately and is not imported into the checked library.

The theorem-coverage script concerns the supplied manuscript's own new
mathematical results. Bibliographic assertions and external cited results
are not certified. See README and the dependency map for the exact formal
counterparts and proof-route differences.
