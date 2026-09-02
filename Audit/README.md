# Audit comparator surface

Mathlib-only comparator challenge for the library's main theorem, in the pattern of the
`CoarseGraining` repository and checked with
[`leanprover/comparator`](https://github.com/leanprover/comparator).

| Directory | Checked theorem |
| --- | --- |
| `ContinuousMarkovProcess/` | `MarkovProcessChallenge.existsUnique_continuousMarkovProcess` |
| `BrownianMotion/` | `BrownianMotionChallenge.brownianMotion` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every definition needed to
read its theorem, states the theorem, and ends with one `sorry`, the proof being checked. For
`ContinuousMarkovProcess/` the vocabulary is sub-Markov kernel semigroups, conservativity, the
`C₀` action and the Feller property, finite-dimensional distributions by iterated composition,
the Kolmogorov moment criterion, and continuous-path space with its Borel sigma-algebra; for
`BrownianMotion/` it is the Gaussian heat kernels, their finite-dimensional distributions,
continuous-path space, and the predicates `HasIndepIncrements` (Mathlib's definition, verbatim)
and `IsBrownianReal` (the form Mathlib proves equivalent to its definition). `SolutionBasic.lean` is a verbatim copy of that
vocabulary, still Mathlib-only; `Solution.lean` imports the library and `SolutionBasic` and
proves the byte-identical statement through private bridges between the challenge's
definitions and the library's.

Presentation deltas between each challenge and the library statement are enumerated in the
module docstring of that `Challenge.lean`.

**Status.** Passing. With the comparator built from
[`leanprover/comparator`](https://github.com/leanprover/comparator) at commit `5756749`
(`lake build` in its checkout; `landrun` and `lean4export` on the path), the run

```bash
lake env <comparator checkout>/.lake/build/bin/comparator Audit/ContinuousMarkovProcess/comparator.json
lake env <comparator checkout>/.lake/build/bin/comparator Audit/BrownianMotion/comparator.json
```

from the repository root prints `Lean default kernel accepts the solution` and
`Your solution is okay!` for each pair, at the library commit recorded in the git history of
this file. The
challenge's helper lemmas are public rather than `private` because the comparator compares
constants by name and private names are module-mangled.
