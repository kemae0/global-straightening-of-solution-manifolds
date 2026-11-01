# Corrections to the supplied manuscript

The current supplied revision, titled *Global Straightening of Solution
Manifolds for State-Dependent Delay Equations*, is preserved byte for byte
in `manuscript/paper_revised.tex`. Its hash and the current formalization
target's hash are recorded in `verification/provenance.json`.

## Reflection wording resolved in the latest revision

The sentence before the endpoint-reflection example in the preceding draft said the zero-atom
condition is not necessary for "the diffeomorphism in Theorem 3.3"
(the theorem labelled `thm:no-atom`). Read as referring to all that theorem's
conclusions, this was false. For `f = 2D`, the example `A = I - 2QD` is an
ambient continuous linear involution satisfying `D A = -D`, but its
complexified derivative has `-1` in its spectrum. More generally, every
C¹ chart with this defect identity on a nonempty open domain has `-1` in
its derivative spectrum, so it cannot have spectrum `{1}`.

`EndpointReflection.lean` constructs the exact displayed involution and
proves `neg_one_mem_complexified_spectrum_of_endpoint_flip` and
`C1Straightening.twice_endpoint_spectrum_obstruction`. This issue was
reported to the user. The author then revised the paragraph to distinguish
the full theorem's conclusions from existence of a C¹ diffeomorphism with
the defect identity. The latest paragraph matches the checked result.
Both `paper_revised.tex` and the certificate alias `paper_corrected.tex`
now preserve that latest supplied text byte for byte, without agent edits.

## Historical corrections

The user approved the following corrections to the earlier manuscript.
The revised draft incorporates these repairs. Their Lean counterexamples
remain in the library as regression certificates.

1. **Spectrum equality in the zero space is false.** The coordinate lemma
   and Hilbert theorem allow a zero state space but assert spectrum `{1}`.
   The identity on the zero complex space has empty spectrum. Require a
   nontrivial state space for equality, or use inclusion in `{1}`. The
   counterexample is proved in `Counterexamples.lean`. Spatial straightening
   and the isotopy do not require nontriviality.
   `LiteralManuscriptObstructions.lean` also checks the actual zero Hilbert
   history space, verifies property (e) for zero feedback on the whole open
   space, and proves that no proposed chart can have the written spectrum.

2. **The adapted-approximation proof needs the empty-domain case.** It
   chooses a sequence of points in `U`, which is impossible for `U = ∅`.
   The formal proof uses a countable, possibly empty dense subfamily of the
   derivative image and includes empty domains.

3. **Full support does not make zero-weight denominators positive.** A
   partition of unity may contain identically zero weights. Full support
   implies `∫ ψ dν > 0` only for a nonzero nonnegative continuous weight.
   Remove zero weights or define their averages to be zero. The formal
   Markov operators use the latter convention and prove all convergence
   and contraction estimates with that convention.
   `full_support_partition_zero_denominator` gives an explicit partition
   for the full-support interval Lebesgue measure with a zero denominator.

4. **The endpoint-identity impossibility comparison needs additional
   hypotheses.** For `f(φ) = φ′(0)`, the claim that no ambient straightening
   exists requires a nonempty domain and a nontrivial state space. The
   empty-domain identity chart and the chart for a subsingleton codomain
   are constructed in `EndpointObstruction.lean`. The corrected
   impossibility statement is also proved there.

The formal proof routes differ in two additional, non-corrective ways.
The first version used direct operator-norm closure instead of the
intermediate total-variation argument. Actual signed-measure duality,
total-variation continuity and full-image domination are now checked, and
the terminal existence proof has been connected to that route.
The general observation induction does not need nested sampling grids.
The Hilbert proof nevertheless now uses the manuscript's degree-4^m
operators, their actual ranges and nestedness, and the displayed distance
cores, smooth cutoffs and saturation formula. These are all separately
checked and connected to the existence theorem.
