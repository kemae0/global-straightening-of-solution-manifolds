# Global straightening of solution manifolds — Lean formalization

Kernel-checked counterparts of the supplied manuscript's new existence
theorems, coordinate construction, and application corollaries, with the
corrections in [MANUSCRIPT_CORRECTIONS.md](MANUSCRIPT_CORRECTIONS.md).
The original LaTeX article is not certified verbatim.

The main results are proved from their analytic assumptions on genuine
complete normed C¹ history spaces. They are not axioms, proposition
aliases supplied as hypotheses, or proofs containing `sorry`.

## Main certificates

All names below are in the `GlobalRegularization` namespace.

| Result | Lean theorem |
| --- | --- |
| Principal property-(e) theorem, every finite state dimension | `mainClaim` |
| Stronger terminal-atom theorem, localization, uniform bound, isotopy and complex spectrum | `terminal_atom_full_straightening` |
| Zero-dimensional version with spectrum inclusion | `terminal_atom_full_straightening_spectrum_inclusion` |
| Arbitrary separable real Hilbert state space, including the actual complex spectrum | `property_e_Hilbert_full_straightening` |
| Hilbert version allowing the zero space | `property_e_Hilbert_straightening_spectrum_inclusion` |
| All-level identities, split fiber charts, continuous complements and codimension | `terminal_atom_fiber_geometry` |
| Invertible endpoint-derivative coupling | `terminal_atom_endpoint_coupling_of_isUnit` |
| Arbitrary Banach remote-observation ranges | `remote_observation_full_straightening` |
| Concrete past-derivative example | `pastDerivative_full_straightening` |
| Failure of continuous-history derivative extension for that example | `scalarPastDerivativeFeedback_no_extended_derivative_at_zero` |

Spectrum equality requires positive finite state dimension or a nontrivial
Hilbert state space. All spatial conclusions and spectrum inclusion hold
also in the zero space. Empty open domains are included.

The Hilbert proof constructs C¹ cutoffs near arbitrary closed cores and
bounded C¹ saturation maps. It does not assume compactness of bounded
Hilbert-valued ranges or of infinite-dimensional balls.

## Reproduce verification

The project pins Lean **4.24.0** and mathlib commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7` (tag `v4.24.0`).

```text
lake exe cache get
lake build
lake env lean scripts/Audit.lean
lake env lean scripts/MainCertificate.lean
lake env lean scripts/PaperCertificate.lean
```

On the original Windows workspace, the local-distribution helper is:

```powershell
.\scripts\Lean.ps1 build
.\scripts\Lean.ps1 env lean scripts/Audit.lean
.\scripts\Lean.ps1 env lean scripts/PaperCertificate.lean
```

The helper uses `.toolchain/` when present and otherwise uses the installed
Lean/Lake. Dependencies and compiler binaries are not part of the source
publication. GitHub Actions repeats the build and certificate checks.

`Audit.lean` traverses the transitive axiom dependencies of every declaration
in the project namespace. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted. It rejects `sorryAx` and additional axioms.

## Proof organization and differences

[PROOF_OBLIGATIONS.md](PROOF_OBLIGATIONS.md) maps the manuscript's dependency
chain to checked modules. [FORMALIZATION_AUDIT.md](FORMALIZATION_AUDIT.md)
explains scope, representations, and the verification evidence.

The principal finite-state proof has a direct Bernstein route. The stronger
terminal theorem constructs positive Markov averages, terminal cutoffs and
finite-rank reconstructed history operators. Adjoint approximation extends
from a countable dense family directly in operator norm. This replaces the
manuscript's intermediate argument about continuity of the measure component
in total variation and domination of every measure in the full derivative
image; those intermediate measure claims are not separately certified here.

The observation induction does not require nested sampling grids. This
allows ordinary increasing Bernstein degrees in the Hilbert proof.

The manuscript's bibliography, historical claims and cited semiflow theory
are background, not formalized results of this repository. Signed integrals
are represented as differences of integrals against finite positive Borel
measures. Split-submanifold geometry is certified through explicit C¹ kernel
charts, tangent maps and finite-codimensional complements.

The unmodified input archive is preserved in the original local workspace,
outside the checked library. Input hashes are recorded in
`verification/provenance.json`. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)
for the mathlib proof adaptation notice.
