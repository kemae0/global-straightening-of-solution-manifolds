# Corrections to the supplied manuscript

These issues were reported during formalization. The original manuscript
has been preserved; the Lean statements implement the corrections below.

1. **Spectrum equality in the zero space is false.** The coordinate lemma
   and Hilbert theorem allow a zero state space but assert spectrum `{1}`.
   The identity on the zero complex space has empty spectrum. Require a
   nontrivial state space for equality, or use inclusion in `{1}`. The
   counterexample is proved in `Counterexamples.lean`. Spatial straightening
   and the isotopy do not require nontriviality.

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

4. **The endpoint-identity impossibility comparison needs additional
   hypotheses.** For `f(φ) = φ′(0)`, the claim that no ambient straightening
   exists requires a nonempty domain and a nontrivial state space. The
   empty-domain identity chart and the chart for a subsingleton codomain
   are constructed in `EndpointObstruction.lean`. The corrected
   impossibility statement is also proved there.

The formal proof routes differ in two additional, non-corrective ways.
Adjoint convergence extends from a dense family directly in operator norm,
avoiding the intermediate total-variation continuity argument. The
observation induction does not need nested sampling grids, so the Hilbert
construction uses ordinary increasing Bernstein degrees. These changes do
not weaken the hypotheses or conclusions of the stated existence results.
