# Conventions

This page records the conventions the `MarkovProcess` source follows, so that a reader can
predict what a statement means without reading its proof, and a contributor can match the
existing style. The rules that a change must satisfy to be merged are in `CONTRIBUTING.md`; this
page is descriptive.

## Ambient assumptions

The library is written over a state space `alpha` carrying, in the fullest case, the block

```lean
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [StandardBorelSpace alpha] [Nonempty alpha]
```

Read as mathematics: `alpha` is a nonempty, locally compact Polish space (complete, second
countable, metric), equipped with its Borel sigma-algebra and known to be standard Borel. Each
assumption is load-bearing somewhere:

- `MetricSpace`, `CompleteSpace`, `SecondCountableTopology` — completeness and separability are
  what make continuous-path space Polish (`Path/Polish.lean`), and the Kolmogorov continuity
  argument in `Continuity/` is a metric-space argument.
- `MeasurableSpace` with `BorelSpace` — every measurability statement is about the Borel
  sigma-algebra of the topology, never about an independently chosen one.
- `LocallyCompactSpace` — required by the Feller results, which test measures against compactly
  supported and `C₀` functions. Files that do not use compact tests omit it; `Trajectory/Basic.lean`
  is the notable example, using the block above **without** `[LocallyCompactSpace alpha]`.
- `StandardBorelSpace` and `Nonempty` — used for disintegration and for the measurable extension
  that needs a fallback point.

Each file states exactly the block it needs. When a section variable turns out to be unused,
the `unusedSectionVars` linter reports it and the file records the fact with an `omit` line
before the declaration, as in

```lean
omit [CompleteSpace alpha] [LocallyCompactSpace alpha] [StandardBorelSpace alpha]
  [Nonempty alpha] in
```

Do not delete an assumption from the shared block to satisfy one declaration; use `omit`.

## Time, paths, and filtrations

- **Time is `NNReal`.** Transition kernels are indexed by `NNReal`, semigroups are
  `NNReal`-indexed, and path space is indexed by `NNReal`.
- **`DenseTime` is `NNRat`**, the countable dense set of times used to build the trajectory. It
  reaches physical time through the order embedding `MarkovProcess.DenseTime.castOrderEmbedding :
  DenseTime ↪o NNReal`, and is enumerated by `MarkovProcess.DenseTime.enumeration : ℕ ≃ DenseTime`.
  A statement about "rational times" is a statement about `DenseTime`; a statement about "physical
  times" or "all times" is about `NNReal`.
- **`ContinuousPath alpha` is `C(NNReal, alpha)`**, an `abbrev`, carrying the compact-open
  topology. Path space is given the Borel sigma-algebra of that topology (see local instances
  below), not a product or cylinder sigma-algebra.
- **Shifts.** `ContinuousPath.shift S omega` satisfies `shift S omega t = omega (S + t)`: shifting
  by `S` discards the past before `S` and re-times the future to start at zero.
- **The canonical filtration** is `ContinuousPath.canonicalFiltration`, the supremum over `s ≤ t`
  of the comaps of the time-`s` coordinate. It is a Mathlib `Filtration NNReal (borel (ContinuousPath alpha))`.
- **Chapman–Kolmogorov orientation.** `SubMarkovKernelSemigroup` states the semigroup law as
  `kernel (s + t) = (kernel t).comp (kernel s)`, matching Mathlib's convention that `η.comp κ`
  applies `κ` first. The associated operator sends `f` to `x ↦ ∫ y, f y ∂K x`.
- **Conservativity is separate.** `SubMarkovKernelSemigroup` only assumes `IsSubMarkovKernel` at
  each time; `IsConservative P` is the additional predicate `∀ t x, P t x univ = 1`. Statements
  that need mass one take `hP : P.IsConservative` explicitly, and the killed case is handled by
  the cemetery extension in `DenseTime/` and by the lifetime paths in `Lifetime/`.

## Stopping-time conventions

Mathlib's `MeasureTheory.IsStoppingTime` takes a map into `WithTop ι`, so an `ι`-valued stopping
time must be coerced. This library works only with **finite** stopping times, and encodes that in
the type: the time itself is `NNReal`-valued, and only the coercion is `WithTop`-valued.

```lean
(T : ContinuousPath alpha → NNReal)
(hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
  (fun omega ↦ (T omega : WithTop NNReal)))
```

Consequences to keep in mind when reading or adding a statement:

- Because `T` lands in `NNReal`, `T omega` is finite for every path, and the coercion is never
  `⊤`. The `Main.lean` API is stated for finite stopping times; the only results for a
  `WithTop`-valued stopping time that may be infinite are those of `Trajectory/StoppingLtTop.lean`,
  on the event `{τ < ⊤}` with the finite value written `(τ ω).untopD 0`.
- **The stopped sigma-algebra is Mathlib's** `MeasureTheory.IsStoppingTime.measurableSpace`,
  written `hT.measurableSpace`. It is never redefined here. `hT.measurableSpace_le` gives the
  comparison with the ambient Borel sigma-algebra, and `IsStoppingTime.measurableSpace_mono`
  compares the stopped sigma-algebras of two ordered stopping times — that monotonicity is what
  lets an event in the sigma-algebra of `T` be used at each dyadic ceiling `T ≤ dyadicCeiling n ∘ T`.
- Since `T omega` is a plain `NNReal`, the state at the stopping time is written directly as
  `omega (T omega)`, and the shifted path as `ContinuousPath.shift (T omega) omega`. Their
  measurability comes from `ContinuousPath.measurable_eval_stoppingTime_borel` and
  `ContinuousPath.measurable_shift_stoppingTime`.
- The approximation scheme is fixed: `MarkovProcess.dyadicCeiling n` sends a time to the least
  point of `2⁻ⁿ ℕ` above it. `isStoppingTime_dyadicCeiling` makes each level a stopping time for
  the same filtration, `countable_range_dyadicCeiling_comp` gives countable range,
  `le_dyadicCeiling` and `antitone_dyadicCeiling` give approximation from above, and
  `tendsto_dyadicCeiling` gives convergence. A general finite stopping time is always handled by
  reducing to countable range this way.

## Naming local instances

Path space carries the Borel sigma-algebra of the compact-open topology as a global instance
(`Path/Basic.lean`); the library declares no local instance for it. Where an auxiliary local
instance is unavoidable, **it is named**, and the name includes the file or theorem context, so
that the auto-generated names of two anonymous instances can never collide across modules:

```lean
local instance continuousPathTrajectoryFellerStoppingRestartMeasurableSpace :
    MeasurableSpace (ContinuousPath alpha) := borel _
local instance continuousPathTrajectoryFellerStoppingRestartBorelSpace :
    BorelSpace (ContinuousPath alpha) := ⟨rfl⟩
```

The reason is mechanical. An anonymous `local instance` gets an auto-generated name derived from
its type, so two files that both write `local instance : MeasurableSpace (ContinuousPath alpha)`
generate the *same* name, and importing both produces a declaration collision. Naming them after
the file removes the collision and makes the instance greppable when a typeclass search goes
wrong. A handful of older files still carry anonymous ones; those are a defect to be fixed, not a
precedent.

The same convention applies to any `letI`/`haveI` introduced for a proof: prefer a named
`local instance` at the top of the section over a repeated anonymous one inside proofs.

## Module docstring style

Every file opens with the Mathlib copyright header, then a module docstring:

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import ...

/-!
# Title of the file's subject

One or two sentences saying what the file establishes, and by what route if the route matters to
a reader deciding whether to import it.

A closing sentence naming what the file does *not* claim.
-/
```

Three points of style, all of which the tree follows:

1. **The title is the subject, not the file name.** "Dyadic ceiling approximation of finite
   stopping times", not "StoppingTimeDyadicCeiling". `MODULES.md` is generated from these titles
   and first sentences, so they double as the module index.
2. **The body says what is established**, in mathematical language, including the shape of the
   hypotheses when they are unusual. Where a result is conditional — most of `Trajectory/` is
   conditional on the Kolmogorov hypothesis `hK` — the docstring says so rather than leaving the
   reader to discover it in the signature.
3. **The closing sentence bounds the claim.** Files in this library are deliberately explicit
   about the stronger statement they are *not* making: "makes no Hunt-process assertion", "does
   not cover a `WithTop`-valued time that can be infinite", "constructs no probability law",
   "proves no probabilistic statement". This is the convention that keeps an infrastructure file
   from being mistaken for a headline theorem.

Declaration docstrings follow the same discipline: state the content of the declaration, in a
sentence that would be true read aloud without the surrounding file. Every public `theorem`,
`def`, `structure`, `abbrev` and named `instance` has one.

## Naming of declarations

Names follow Mathlib conventions as far as the tree has been converted: lower camel case for
data (`continuousPathTrajectory`, `dyadicCeiling`, `denseTimePrefixKernel`), upper camel case for
types and predicates (`SubMarkovKernelSemigroup`, `IsConservative`, `IsFellerKernelSemigroup`,
`LifetimePath`), and theorem names that describe the statement in the order the symbols appear
(`continuousPathTrajectory_restrict_map_shift_stoppingTime`,
`isNonexplosive_iff_coordinate_nat_ne_delta`, `tendsto_dyadicCeiling`).

Theorems whose natural home is a predicate are declared under it, so that dot notation works on a
hypothesis: `hFeller.continuousPathTrajectory_restrict_map_shift` and `hP.isMarkovKernel` read as
uses of the hypothesis rather than as free-floating lemmas. Names follow Mathlib's conventions
(snake_case of lowerCamelCase tokens read from the conclusion, hypotheses after `_of_`,
`_iff`, `_apply`, `_left`/`_right`); a name that departs from them is a bug to report.
