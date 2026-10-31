# Third-party notices

The project depends on mathlib4 at commit
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, licensed under the Apache License,
Version 2.0. A copy of that license is included as `LICENSE.mathlib`.

The proof of `exists_hilbert_C1_positive_support` in
`GlobalRegularization/HilbertPositiveSupport.lean` adapts the countable
bump-sum construction from
`Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean` to separable
Hilbert spaces and C¹ bounds. The original file carries:

> Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
> Released under Apache 2.0 license as described in the file LICENSE.
> Authors: Sébastien Gouëzel

This adaptation replaces compact-support bounds in finite dimension by
the explicitly proved first-derivative bounds for Hilbert radial bumps.

The notice and `LICENSE.mathlib` describe the imported/adapted third-party
material. They do not assign a new license to the user's original sources
or manuscript.
