# MarkovProcess

A **Lean 4** library of sub-Markov transition semigroups, Feller semigroups,
and the continuous-path Markov processes they generate, built on
[`mathlib`](https://github.com/leanprover-community/mathlib4).

[![CI](https://github.com/scottnarmstrong/MarkovProcess/actions/workflows/build.yml/badge.svg)](https://github.com/scottnarmstrong/MarkovProcess/actions/workflows/build.yml)
[![Comparator audit](https://github.com/scottnarmstrong/MarkovProcess/actions/workflows/comparator.yml/badge.svg)](https://github.com/scottnarmstrong/MarkovProcess/actions/workflows/comparator.yml)

## What this is

This repository constructs, from a transition semigroup on a locally compact Polish state space, the
continuous-path Markov process with those transition probabilities, and proves that it is
unique and strong Markov. Everything is stated for every starting point: the process is a
measurable kernel from the state space to path space, and no statement holds only outside an
exceptional set. On that construction the library builds the process killed on leaving an open
set and the gluing of the local resolvents of an exhaustion into a minimal resolvent, the
one-point compactification of a locally compact live space and the process it carries, exit
times and exit laws, Dynkin's formula and optional stopping, and the Feynman-Kac semigroup of a
bounded potential. It contains no PDE and no model-specific assumption, and its only dependency
is Mathlib.

- **249 Lean modules plus the root module `MarkovProcess.lean`, about 45,700 lines** (`MODULES.md`
  lists every module with a one-line description).
- **No `sorry`** anywhere in the library. (The Mathlib-only comparator challenge in `Audit/`
  contains its single intentional statement-level `sorry`, filled by the solution file.)
- **No custom `axiom`.** Every public theorem reduces to Mathlib's three standard foundational
  axioms `propext`, `Classical.choice`, `Quot.sound`.
- Pinned to Lean `v4.26.0` and `mathlib` `v4.26.0`. Builds warning-free under the Lean core
  linters enabled in the lakefile (unused variables and section variables, unused simp arguments,
  unnecessary `simpa`, deprecations); no heartbeat overrides anywhere.

## Main result

The main theorem is exposed, with the whole consumer-facing API, in
[`MarkovProcess/Main.lean`](MarkovProcess/Main.lean). Import `MarkovProcess.Main` to use it.

**Existence and uniqueness of the continuous Markov process.** For every conservative Feller
sub-Markov kernel semigroup `P` on a locally compact Polish space `α` satisfying the Kolmogorov
moment criterion, there is **exactly one** Markov kernel `Q` from `α` to `C([0, ∞), α)` whose
finite-dimensional distributions are those of `P`: for every finite set of times
`I = {t₁ < ⋯ < tₙ}` and every `x`, the law of `(ω(t₁), …, ω(tₙ))` under `Q x` is
`P t₁ (x, ·) ⊗ P (t₂ − t₁) ⊗ ⋯ ⊗ P (tₙ − tₙ₋₁)`. In Lean, verbatim from `Main.lean` (the
`variable` lines are the ambient assumptions in force where the theorem is stated):

<!-- BEGIN verbatim -->
<!-- source: MarkovProcess/Main.lean -->
```lean
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]
...
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
...
variable [LocallyCompactSpace alpha]
...
theorem IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I
```
<!-- END verbatim -->

Every name in this statement is defined in the library or in Mathlib, as follows.

| name | meaning | defined in |
| --- | --- | --- |
| the instance block | `α` is a nonempty complete separable metric space with its Borel sigma-algebra, locally compact where the Feller property is used: a locally compact Polish space | `Main.lean` |
| `SubMarkovKernelSemigroup alpha` | a family of transition kernels `P t : Kernel α α`, `t ≥ 0`, jointly measurable in `(t, x)`, with `P 0` the identity, the Chapman–Kolmogorov law `P (s + t) = P t ∘ P s`, and every `P t x` of mass at most one | [`Kernel/KernelSemigroup.lean`](MarkovProcess/Kernel/KernelSemigroup.lean) |
| `P.IsConservative` | every `P t x` is a probability measure | [`Kernel/KernelSemigroup.lean`](MarkovProcess/Kernel/KernelSemigroup.lean) |
| `P.IsFellerKernelSemigroup` | integration against `P t` maps `C₀(α, ℝ)` into itself (`MapsC0`), and the resulting contractions `c0Operator t` of `C₀(α, ℝ)` have norm-continuous orbits `t ↦ P_t f` (`HasContinuousC0Orbits`) | [`Kernel/C0.lean`](MarkovProcess/Kernel/C0.lean), [`Feller/Semigroup.lean`](MarkovProcess/Feller/Semigroup.lean) |
| `P.HasKolmogorovMoments p q M` | `0 < p`, `1 < q`, and `∫ dist(z, y)^p P h (y, dz) ≤ M · h^q` for every `h ≥ 0` and every `y ∈ α` | [`Kernel/KolmogorovMoments.lean`](MarkovProcess/Kernel/KolmogorovMoments.lean) |
| `Kernel α β`, `IsMarkovKernel Q`, `Q.map f` | Mathlib: a measurable family `x ↦ Q x` of measures on `β`; each `Q x` a probability measure; the pushforward of each `Q x` by `f` | Mathlib, `Probability/Kernel` |
| `ContinuousPath alpha` | `C(NNReal, α)`, the continuous paths on `[0, ∞)` with the compact-open topology and its Borel sigma-algebra; Polish and standard Borel ([`Path/Polish.lean`](MarkovProcess/Path/Polish.lean)) | [`Path/Basic.lean`](MarkovProcess/Path/Basic.lean) |
| `ContinuousPath.finsetEvaluation I` | `ω ↦ (ω t)_{t ∈ I}`, the path read at the times of the finite set `I` | [`Main.lean`](MarkovProcess/Main.lean) |
| `finiteSetKernel P I` | the law of `(ω t)_{t ∈ I}` prescribed by `P`: along the increasing enumeration `t₁ < ⋯ < tₙ` of `I`, sample `P t₁` from `x`, then `P (t₂ − t₁)` from the sampled point, and so on (`finiteTimeKernel`, by recursion on the number of times) | [`FiniteTime/Kernel.lean`](MarkovProcess/FiniteTime/Kernel.lean), [`FiniteTime/ProjectiveFamily.lean`](MarkovProcess/FiniteTime/ProjectiveFamily.lean) |

<details>
<summary>The Lean definitions behind these names, verbatim from the source (about a hundred lines; checked against the source in CI)</summary>

<!-- BEGIN verbatim -->
<!-- source: MarkovProcess/Kernel/KernelSemigroup.lean -->
```lean
structure SubMarkovKernelSemigroup (α : Type*) [MeasurableSpace α] where
  /-- The transition kernel at a nonnegative time. -/
  kernel : NNReal → Kernel α α
  /-- Joint measurability in time and starting point. -/
  measurable_kernel : Measurable fun p : NNReal × α ↦ kernel p.1 p.2
  /-- At time zero the transition kernel is the identity kernel. -/
  kernel_zero : kernel 0 = Kernel.id
  /-- The Chapman--Kolmogorov law, in Mathlib's kernel-composition orientation. -/
  kernel_add : ∀ s t, kernel (s + t) = (kernel t).comp (kernel s)
  /-- Every transition measure has mass at most one. -/
  isSubMarkovKernel : ∀ t, IsSubMarkovKernel (kernel t)
...
/-- A transition-kernel semigroup is conservative when no mass is lost. -/
def IsConservative : Prop :=
  ∀ t x, P t x univ = 1
```

<!-- source: MarkovProcess/Kernel/Integral.lean -->
```lean
/-- The raw real-valued integral of `f` against the measure `κ x`. -/
noncomputable def kernelIntegral (κ : Kernel α α) (f : α → ℝ) (x : α) : ℝ :=
  ∫ y, f y ∂κ x
```

<!-- source: MarkovProcess/Kernel/C0.lean -->
```lean
/-- A kernel semigroup maps `C₀(α, ℝ)` into itself when its raw kernel integral is continuous
and vanishes at infinity at every time. -/
def MapsC0 (P : SubMarkovKernelSemigroup α) : Prop :=
  ∀ t (f : C₀(α, ℝ)),
    Continuous (kernelIntegral (P t) f) ∧
      Tendsto (kernelIntegral (P t) f) (cocompact α) (nhds 0)
...
/-- The exact `C₀` representative obtained by integrating against `P t`. -/
noncomputable def c0KernelIntegral (t : NNReal) (f : C₀(α, ℝ)) : C₀(α, ℝ) where
  toFun := kernelIntegral (P t) f
  continuous_toFun := (hC0 t f).1
  zero_at_infty' := (hC0 t f).2
...
/-- The kernel integral as a contraction on real continuous functions vanishing at infinity. -/
noncomputable def c0Operator (t : NNReal) : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ) :=
...
```

<!-- source: MarkovProcess/Feller/Semigroup.lean -->
```lean
/-- The `C₀` kernel operators have continuous time orbits in the `C₀` norm. This is an
additional hypothesis beyond the spatial `MapsC0` property. -/
def HasContinuousC0Orbits (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0) : Prop :=
  ∀ f : C₀(α, ℝ), Continuous fun t : NNReal ↦ P.c0Operator hC0 t f
...
/-- A sub-Markov kernel semigroup on a locally compact Hausdorff space has the `C₀`
Feller-semigroup properties when it maps `C₀` into itself and its resulting `C₀` operator orbits
are continuous in time. Conservativity is not part of this predicate. -/
def IsFellerKernelSemigroup (P : SubMarkovKernelSemigroup α)
    [LocallyCompactSpace α] [T2Space α] : Prop :=
  ∃ hC0 : P.MapsC0, P.HasContinuousC0Orbits hC0
```

<!-- source: MarkovProcess/Kernel/KolmogorovMoments.lean -->
```lean
def HasKolmogorovMoments (P : SubMarkovKernelSemigroup alpha) (p q : ℝ) (M : ℝ≥0) : Prop :=
  0 < p ∧ 1 < q ∧
    ∀ (h : ℝ≥0) (y : alpha), ∫⁻ z, edist z y ^ p ∂(P h y) ≤ M * (h : ℝ≥0∞) ^ q
```

<!-- source: MarkovProcess/Path/Basic.lean -->
```lean
/-- Continuous paths on nonnegative real time, with the compact-open topology. -/
abbrev ContinuousPath (alpha : Type*) [TopologicalSpace alpha] := C(NNReal, alpha)
```

<!-- source: MarkovProcess/Trajectory/AllTimeFiniteMarginals.lean -->
```lean
def finiteEvaluation {ι α : Type*} [TopologicalSpace α]
    (τ : ι → NNReal) : ContinuousPath α → (ι → α) :=
  fun path i ↦ path (τ i)
```

<!-- source: MarkovProcess/Main.lean -->
```lean
/-- Evaluate a continuous path simultaneously at every time of a finite set of nonnegative
times, indexing the result by that set. -/
abbrev finsetEvaluation (I : Finset NNReal) : ContinuousPath alpha → (I → alpha) :=
  finiteEvaluation (fun t : I ↦ (t : NNReal))
```

<!-- source: MarkovProcess/Time/FiniteOrderedTimes.lean -->
```lean
abbrev FiniteOrderedTimes (n : ℕ) := Fin n ↪o NNReal
```

<!-- source: MarkovProcess/FiniteTime/Kernel.lean -->
```lean
/-- The finite-time kernel obtained by recursively sampling a strictly ordered family of times. -/
noncomputable def finiteTimeKernel (P : SubMarkovKernelSemigroup α) :
    {n : ℕ} → FiniteOrderedTimes n → Kernel α (Fin n → α)
  | 0, _ => Kernel.const α (Measure.dirac (FiniteOrderedTimes.emptyPath α))
  | n + 1, times =>
      Kernel.mapOfMeasurable
        (P (times 0) ⊗ₖ Kernel.prodMkLeft α (finiteTimeKernel P times.relativeTail))
        (fun z ↦ @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2) measurable_finCons
```

<!-- source: MarkovProcess/FiniteTime/ProjectiveFamily.lean -->
```lean
/-- The increasing enumeration of a finite set of nonnegative times. -/
noncomputable def finiteSetTimes (I : Finset NNReal) : FiniteOrderedTimes I.card :=
  I.orderEmbOfFin rfl
...
/-- Reindex an ordered coordinate path by its finite set of times. -/
noncomputable def orderedPathToFiniteSet (I : Finset NNReal) (path : Fin I.card → α) : I → α :=
  fun t ↦ path ((I.orderIsoOfFin rfl).symm t)
...
/-- The finite-time kernel indexed by a finite set of times. -/
noncomputable def finiteSetKernel (P : SubMarkovKernelSemigroup α) (I : Finset NNReal) :
    Kernel α (I → α) :=
  Kernel.mapOfMeasurable (finiteTimeKernel P (finiteSetTimes I))
    (orderedPathToFiniteSet I) (measurable_orderedPathToFiniteSet I)
```
<!-- END verbatim -->

</details>

The Mathlib-only restatement
[`Audit/ContinuousMarkovProcess/Challenge.lean`](Audit/ContinuousMarkovProcess/Challenge.lean)
(281 lines) unfolds every one of these definitions to Mathlib primitives and is verified against
the library by `leanprover/comparator` (see below).

The unique kernel is the library's canonical object `continuousProcess P hP`. Its properties
are exposed as separately quotable theorems about that object, all in `Main.lean`:

| property | theorem |
| --- | --- |
| starts at its argument: the law of `ω(0)` under `Q x` is `δₓ` | `continuousProcess_map_eval_zero` |
| finite-dimensional distributions at all real times | `continuousProcess_map_finiteEvaluation` |
| shift identity `Q.map (shift s) = Q ∘ P s` | `continuousProcess_map_shift` |
| Markov property at a deterministic time, as restart of the restricted law | `continuousProcess_restrict_map_shift` |
| Markov property at a deterministic time, as a conditional expectation | `continuousProcess_condExp_shift` |
| **strong Markov property** at every finite stopping time, restart form | `continuousProcess_restrict_map_shift_stoppingTime` |
| **strong Markov property** at every finite stopping time, conditional-expectation form | `continuousProcess_condExp_shift_stoppingTime` |
| uniqueness as an equation: any finite kernel with these marginals equals `continuousProcess` | `eq_continuousProcess_of_map_finiteEvaluation` |
| the same with marginals at rational times only, and without the Feller hypothesis | `eq_continuousProcess_of_map_finiteEvaluation_denseTime`, `existsUnique_continuousProcess_denseTime` |
| independence of the construction from its fallback path | `continuousProcess_eq_continuousPathTrajectory` |

The strong Markov property reads: for every finite stopping time `T` of the canonical
filtration (an `NNReal`-valued map whose coercion to `WithTop NNReal` is a Mathlib
`IsStoppingTime`), every event `A` in Mathlib's stopped sigma-algebra `hT.measurableSpace`, and
every bounded strongly measurable functional `F` on paths,

> `E_x [ F(ω(T + ·)) | 𝓕_T ] = E_{ω(T)} [ F ]`  almost surely under `Q x`,

together with the corresponding identity of measures for the law of the shifted path
restricted to `A`.

The Feller and local-compactness hypotheses enter only through the identification of marginals
and restarts at irrational times; every Markov and strong Markov statement in `Main.lean` carries
them, while the rational-time statements (`_denseTime` names, `Trajectory/RationalShift.lean`,
`Trajectory/DenseStoppingRestart.lean`) and all uniqueness statements are proved without them.
The Feller-free companion `existsUnique_continuousProcess_denseTime` states existence and
uniqueness with marginals prescribed at rational times only, under conservativity and the moment
criterion alone.

## More headline theorems

One statement per layer of the library, verbatim from the source with the `variable` lines in
force (checked in CI); the vocabulary is that of the main theorem, and the complete API is in the
consumer guide. `hK : P.KolmogorovRegular hP` is the regularity of the process, supplied by the
moment criterion through `KolmogorovRegular.of_hasKolmogorovMoments`.

### The strong Markov property

For every finite stopping time `T` of the canonical filtration on path space (an `NNReal`-valued
map whose coercion to `WithTop NNReal` is a Mathlib stopping time), every bounded strongly
measurable `F` on paths with values in a Banach space, and every starting point `x`, the
conditional expectation of `F(ω(T + ·))` given the stopped sigma-algebra is `E_{ω(T)} F`, almost
surely under `Q x`. No augmentation of the filtration is involved.

<!-- BEGIN verbatim -->
<!-- source: MarkovProcess/Main.lean -->
```lean
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]
...
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
...
variable [LocallyCompactSpace alpha]
...
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
...
theorem IsFellerKernelSemigroup.continuousProcess_condExp_shift_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : ℝ) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((continuousProcess P hP) x)[fun omega ↦
        F (ContinuousPath.shift (T omega) omega)|hT.measurableSpace] =ᵐ[
      (continuousProcess P hP) x]
      fun omega ↦ ∫ eta, F eta ∂(continuousProcess P hP) (omega (T omega))
```
<!-- END verbatim -->

### Dynkin's formula and the harmonic representation

For `f` in the domain of the generator `L` of the `C₀` semigroup of `P`,
`E_x f(ω_t) − f(x) = E_x ∫₀ᵗ (L f)(ω_s) ds`; and if `L f = 0` on an open set `U`, then `f(x)` is
the expectation of `f` at the exit time of `U`, truncated at any horizon `K`.

<!-- BEGIN verbatim -->
<!-- source: MarkovProcess/Trajectory/Dynkin.lean -->
```lean
theorem IsFellerKernelSemigroup.integral_eval_sub_eq_integral_integral_generator
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) (x : alpha) :
    ∫ omega, (f : C₀(alpha, ℝ)) (omega t) ∂(IsConservative.continuousProcess P hP x) -
        (f : C₀(alpha, ℝ)) x =
      ∫ omega, (∫ s in (0 : ℝ)..t, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
        ∂(IsConservative.continuousProcess P hP x)
```

<!-- source: MarkovProcess/Trajectory/HarmonicRepresentation.lean -->
```lean
theorem IsFellerKernelSemigroup.integral_eval_exitTimeTrunc_eq_of_generator_eq_zero
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y = 0) (K : NNReal) (x : alpha) :
    ∫ omega, (f : C₀(alpha, ℝ)) (omega (ContinuousPath.exitTimeTrunc U K omega))
        ∂(IsConservative.continuousProcess P hP x) = (f : C₀(alpha, ℝ)) x
```
<!-- END verbatim -->

### Hille–Yosida, in both directions and in kernel form

The generator of the semigroup generated by a contractive resolvent `R` on a Banach space is the
operator with resolvent `R`: its domain is the range of `R_μ` and `L (R_μ g) = μ R_μ g − g`. A
strongly continuous contraction semigroup is determined by its generator. On the kernel side, a
positive contractive resolvent on `C₀(X, ℝ)` (the resolvent identity, the Hille–Yosida bound,
dense range, positivity) is represented by a Feller kernel semigroup, and the resolvent of the
`C₀` semigroup of that kernel semigroup is the resolvent one started from. Conversely, every
strongly continuous contraction semigroup is generated by its own resolvent
(`generatedSemigroup_toContractiveResolvent` in `Semigroup/ResolventGeneration.lean`).

<!-- BEGIN verbatim -->
<!-- source: MarkovProcess/Semigroup/GeneratorResolvent.lean -->
```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
...
theorem generatorDomain_eq_range (R : ContractiveResolvent E) (μ : PositiveShift) :
    (R.generatedSemigroup.generatorDomain : Set E) = Set.range (R.operator μ)
...
theorem generator_operator_apply (R : ContractiveResolvent E) (μ : PositiveShift) (y : E) :
    R.generatedSemigroup.generator ⟨R.operator μ y, R.operator_mem_generatorDomain μ y⟩ =
      (μ : ℝ) • R.operator μ y - y
```

<!-- source: MarkovProcess/Semigroup/GeneratorUniqueness.lean -->
```lean
variable (S T : StronglyContinuousContractionSemigroup E)
...
variable [CompleteSpace E]
...
theorem ext_of_generator (hdom : S.generatorDomain = T.generatorDomain)
    (hgen : ∀ (f : E) (hS : f ∈ S.generatorDomain) (hT : f ∈ T.generatorDomain),
      S.generator ⟨f, hS⟩ = T.generator ⟨f, hT⟩) :
    S = T
```

<!-- source: MarkovProcess/Kernel/PositiveC0Resolvent.lean -->
```lean
variable (R : PositiveC0ContractiveResolvent X)
...
variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
...
noncomputable def kernelSemigroup : SubMarkovKernelSemigroup X
...
theorem isFellerKernelSemigroup_kernelSemigroup : R.kernelSemigroup.IsFellerKernelSemigroup
```

<!-- source: MarkovProcess/Feller/Resolvent.lean -->
```lean
theorem resolvent_c0Semigroup_kernelSemigroup (μ : Semigroup.PositiveShift) :
    R.isFellerKernelSemigroup_kernelSemigroup.c0Semigroup.resolvent μ =
      R.toContractiveResolvent.operator μ
```
<!-- END verbatim -->

### The Trotter–Kato theorem

For strongly continuous contraction semigroups `S i` on one Banach space, indexed along any
filter, strong convergence of the resolvents at a single positive shift gives strong convergence
of the semigroups, uniformly on every bounded interval of times; the converse holds along a
countably generated filter (`tendsto_resolvent_of_tendsto_operator`).

<!-- BEGIN verbatim -->
<!-- source: MarkovProcess/Semigroup/TrotterKato.lean -->
```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} {l : Filter ι}
...
theorem tendstoUniformlyOn_operator_of_tendsto_resolvent
    {S : ι → StronglyContinuousContractionSemigroup E}
    {S' : StronglyContinuousContractionSemigroup E} {μ : PositiveShift}
    (hres : ∀ y : E, Tendsto (fun i ↦ (S i).resolvent μ y) l (𝓝 (S'.resolvent μ y)))
    (x : E) (b : NNReal) :
    TendstoUniformlyOn (fun i (t : NNReal) ↦ (S i) t x) (fun t ↦ S' t x) l (Set.Iic b)
```
<!-- END verbatim -->

### Weak convergence of Feller processes on path space

If the `C₀` resolvents of conservative Feller semigroups `P i` converge at one shift to that of
`Q`, and all of them satisfy one common Kolmogorov moment bound, then on a proper state space the
path laws converge weakly, as probability measures on `C([0, ∞), α)`, from every starting point.
No Prokhorov theorem is used: the common moment bound gives one compact set of paths carrying all
but `ε` of every law, and on it cylinder functions are dense.

<!-- BEGIN verbatim -->
<!-- source: MarkovProcess/Trajectory/WeakConvergence.lean -->
```lean
variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [ProperSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}
...
theorem tendsto_pathLaw_of_tendsto_resolvent
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative) {p q : ℝ} {M : ℝ≥0}
    (hPmom : ∀ i, (P i).HasKolmogorovMoments p q M) (hQmom : Q.HasKolmogorovMoments p q M)
    {mu : Semigroup.PositiveShift}
    (hres : ∀ f : C₀(alpha, ℝ), Tendsto (fun i ↦ (hP i).c0Semigroup.resolvent mu f) l
      (nhds (hQ.c0Semigroup.resolvent mu f))) (x : alpha) :
    Tendsto (fun i ↦ IsConservative.pathLaw (P i) (hPc i) x) l
      (nhds (IsConservative.pathLaw Q hQc x))
```
<!-- END verbatim -->

### Covariance of a quenched process under an environment symmetry

For a measurably parameterized family `P` of conservative Feller semigroups on `alpha`, indexed
by an environment `theta : Theta` (`hP : P.IsConservative` fibrewise, `hK` its regularity), if
`P` is its own rescaled conjugate along a measurable map `g` of the environment, a homeomorphism
`e` of the state space and a time factor `c > 0`, that is
`P theta t x = ((P (g theta) (c * t)) (e.symm x)).map e`, then the quenched path law is invariant
under the corresponding transformation of environment, starting point and path. Stationarity and
re-gauging covariance of a diffusion in a random environment are the case `c = 1`, with `g` the
environment shift and `e` the spatial translation.

<!-- BEGIN verbatim -->
<!-- source: MarkovProcess/Parameterized/Equivariance.lean -->
```lean
theorem IsConservative.continuousProcess_covariant
    (hFeller : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP)
    {g : Theta → Theta} (hg : Measurable g) {e : alpha ≃ₜ alpha} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P g e c) :
    IsConservative.continuousProcess P hP =
      (Kernel.comap (IsConservative.continuousProcess P hP)
          (fun p : Theta × alpha ↦ (g p.1, e.symm p.2))
          (measurable_reparameterize hg e)).map (ContinuousPath.rescale e c)
```
<!-- END verbatim -->

### Brownian motion, and its generator is half the Laplacian

The heat kernels `x ↦ N(x, t)` on the line form a conservative Feller semigroup satisfying the
moment criterion, so the main theorem produces its process, `brownianMotion`. Under
`brownianMotion x` the centred canonical process `ω ↦ ω t − x` is a Brownian motion: each
`ω t − x` has law `N(0, t)`, the increments over increasing times are independent, and paths
are continuous. Mathlib defines Brownian motion (`IsBrownianReal`, from the formalization of
Degenne, Ledvinka, Marion and Pfaffelhuber) by its Gaussian finite-dimensional laws and
continuous paths, and proves that definition equivalent to the three conditions above
(`HasIndepIncrements.isPreBrownianReal_of_hasLaw` and its converse lemmas); the pinned Mathlib
revision predates these, so the library states the predicate in the equivalent form, with
`HasIndepIncrements` copied verbatim. The generator of the heat semigroup on `C₀(ℝ)` is half the
second derivative on twice continuously differentiable `C₀` functions with `C₀` second
derivative. The existence and uniqueness, the Brownian identification and the uniform limit of
the difference quotients are comparator-verified against a Mathlib-only restatement
(`Audit/BrownianMotion/`).

<!-- BEGIN verbatim -->
<!-- source: MarkovProcess/Examples/HeatSemigroup.lean -->
```lean
theorem heatSemigroup_apply (t : NNReal) (x : ℝ) : heatSemigroup t x = gaussianReal x t
...
theorem isFellerKernelSemigroup_heatSemigroup :
    heatSemigroup.IsFellerKernelSemigroup
...
theorem hasKolmogorovMoments_heatSemigroup :
    heatSemigroup.HasKolmogorovMoments 4 2 gaussianFourthMoment
...
def brownianMotion : Kernel ℝ (ContinuousPath ℝ)
```

<!-- source: MarkovProcess/Examples/BrownianMotion.lean -->
```lean
structure IsBrownianReal {Omega : Type*} [MeasurableSpace Omega]
    (X : NNReal → Omega → ℝ) (P : Measure Omega) : Prop where
  /-- At every time the value has the centred Gaussian law of variance that time. -/
  hasLaw_eval : ∀ t : NNReal, HasLaw (X t) (gaussianReal 0 t) P
  /-- The increments over disjoint consecutive intervals are independent. -/
  hasIndepIncrements : HasIndepIncrements X P
  /-- Almost every trajectory is continuous. -/
  cont : ∀ᵐ omega ∂P, Continuous fun t ↦ X t omega
...
theorem isBrownianReal_brownianMotion (x : ℝ) :
    IsBrownianReal (fun (t : NNReal) (omega : ContinuousPath ℝ) ↦ omega t - x)
      (brownianMotion x)
```

<!-- source: MarkovProcess/Examples/HeatGenerator.lean -->
```lean
theorem generator_heatSemigroup (f g : C₀(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (hg : ∀ x, g x = iteratedDeriv 2 (f : ℝ → ℝ) x) :
    isFellerKernelSemigroup_heatSemigroup.c0Semigroup.generator
      ⟨f, mem_generatorDomain_heatSemigroup f g hf hg⟩ = (2 : ℝ)⁻¹ • g
```
<!-- END verbatim -->

## Consumer guide

[`docs/CONSUMER_GUIDE.md`](docs/CONSUMER_GUIDE.md) is the map from the facts a downstream
project needs to the theorems that deliver them, with a compiled usage example for each theorem
family: obtaining the process, marginals and the starting law, the Markov property at
deterministic times, the strong Markov property at finite stopping times (with the truncated exit
time of an open set as the worked stopping time), uniqueness as an equation, exit times, the
measurably parameterized (quenched) process, the examples, the generator and Dynkin's formula,
the killed process, equivariance and scaling, starting from a resolvent, tightness and weak
continuity of the path law, and convergence of semigroups and processes. Its code blocks are kept
verbatim
in `docs/ConsumerGuide.lean` and compiled by `scripts/check_docs.sh` in CI, so the guide cannot
drift from the library. The guide ends with a list of what the library does not yet contain.
[`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps the standard textbook results to the Lean
declarations, and [`docs/ROADMAP.md`](docs/ROADMAP.md) lists what comes next.

## What is proved along the way

The construction runs through the following layers, each a reusable library in its own right
(directory names in parentheses; see `MODULES.md`).

- **Semigroups on a Banach space** (`Semigroup/`): strongly continuous contraction semigroups,
  contractive resolvents, Yosida approximation and generation of a semigroup from a resolvent,
  Duhamel and exponential bounds; the **generator** of a strongly continuous contraction
  semigroup with its domain, the fundamental identity `S t f - f = ∫₀ᵗ S s (L f) ds`, the
  density of the domain and its closedness (`Semigroup/Generator.lean`,
  `Semigroup/GeneratorClosed.lean`); **both halves of the Hille–Yosida correspondence**: the
  generator of the semigroup generated by a contractive resolvent `R` is the operator with
  resolvent `R`, with domain the range of `R_μ` (`Semigroup/GeneratorResolvent.lean`), a
  strongly continuous contraction semigroup is determined by its generator
  (`Semigroup/GeneratorUniqueness.lean`), the resolvent of a semigroup is the Laplace transform
  of its orbits and inverts `μ − L` (`Semigroup/Resolvent.lean`), and the two round trips
  semigroup → resolvent → semigroup and resolvent → semigroup → resolvent are the identity
  (`Semigroup/ResolventGeneration.lean`); the **Trotter–Kato theorem**: convergence of the
  resolvents at one positive shift gives strong convergence of the semigroups, uniformly on
  bounded time intervals, and conversely (`Semigroup/TrotterKato.lean`).
- **Kernels and their operators** (`Kernel/`): sub-Markov kernels, the kernel semigroup
  structure, its action on `C₀(α)` and on `Lᵖ`, the Riesz representation of positive
  contractions on `C₀(α)` as kernels, conservativity, the Kolmogorov moment criterion.
- **Finite-dimensional distributions** (`Time/`, `FiniteTime/`): strictly ordered finite time
  families, the iterated transition kernels indexed by a finite set of times, their restriction,
  deletion, concatenation and shift identities, projective consistency.
- **The dense-time process** (`DenseTime/`): the Ionescu-Tulcea trajectory on the countable
  dense time set `ℚ≥0` and the identification of all its finite marginals; the cemetery
  extension for killed semigroups.
- **Kolmogorov continuity** (`Continuity/`): the dyadic chaining argument turning the Kolmogorov
  moment bound into an almost surely continuous modification, and the transport of the
  dense-time law to a law on continuous paths; a **quantitative modulus of continuity** for the
  path laws, uniform in the starting point, and the resulting **tightness** of the laws over
  compact sets of starting points, by an Arzelà–Ascoli criterion on `C([0, ∞), α)`, on a proper
  metric state space (closed balls compact) (`Continuity/PathModulus.lean`,
  `Continuity/PathTightness.lean`).
- **Path space** (`Path/`): the compact-open topology, Polish and standard Borel structure,
  the canonical filtration, deterministic and random shifts and their measurability,
  identification of measures and kernels from their rational-time restrictions, dyadic
  ceilings of stopping times.
- **Restart identities** (`Restart/`, `Trajectory/`): the joint law of a rational past and the
  future, restart at rational times, at countable-range stopping times, and, by approximation
  from above with dyadic ceilings, at every finite stopping time, and at a stopping time that may
  be infinite on the event where it is finite; the conditional-expectation bridges;
  **Dynkin's formula** `E_x f(ω_t) - f x = E_x ∫₀ᵗ (L f)(ω_s) ds` for `f` in the
  generator domain of the `C₀` semigroup, the **Dynkin martingale**, a continuous-time
  **optional stopping theorem** in the form `E[M_T] = E[M_0]` for locally bounded right-continuous
  martingales at bounded finite stopping times (`Path/OptionalStopping.lean`), Dynkin's formula at
  such stopping times, the **expected exit time bound** (`Trajectory/Dynkin*.lean`,
  `Trajectory/ExpectedExitTime.lean`), excessive-function supermartingales and their discounted
  finite-exit inequality (`Trajectory/ExcessiveStopping.lean`), the **Feynman–Kac semigroup** for
  bounded nonnegative measurable potentials, including its resolvent perturbation formula and
  comparison with killed resolvents (`Trajectory/FeynmanKac.lean`), the **harmonic and Poisson
  representations** of solutions of
  `L f = 0` and `L f = −g` on an open set, at the exit time truncated at any horizon, and the
  localized Dynkin formula (`Trajectory/HarmonicRepresentation.lean`), the stopped law and the
  **exit distribution** of an open set as kernels (`Trajectory/ExitLaw.lean`), and the **weak
  continuity of the path law** in the starting point on a proper state space, `x ↦ Q x`
  continuous into the probability measures on path space with the weak topology, by cylinder
  approximation on a compact set of paths (`Trajectory/WeakContinuity.lean`); and the
  **convergence of Feller processes**: strong convergence of the `C₀` semigroups gives
  convergence of the finite-dimensional distributions (`Feller/FiniteSetConvergence.lean`,
  `Trajectory/Convergence.lean`), and, under one common Kolmogorov moment bound on a proper
  state space, convergence of the semigroups, or of their resolvents at one shift, gives weak
  convergence of the path laws (`Trajectory/WeakConvergence.lean`), without Prokhorov's theorem.
- **The killed process** (`Killed/`): the transition kernels of the process killed when it
  leaves an open set, `Q_x{t < τ_U, ω_t ∈ ·}`, are sub-Markov, jointly measurable in time and
  starting point, and satisfy the Chapman–Kolmogorov law, forming the **killed semigroup** on
  the open set; exit times of open sets are stopping times of the canonical filtration and behave
  under shifts as `τ ∘ θ_t = τ - t` on the event `{t < τ}` (`Path/ExitTimeShift.lean`); the
  killed process itself is a Markov kernel into lifetime paths whose finite-dimensional
  distributions are those of the killed semigroup with a cemetery state, compatible under nested
  domains (`Killed/Process.lean`, `Killed/Marginals.lean`, `Killed/Nested.lean`); the **killed
  resolvent** is `E_x ∫₀^{τ_U} e^{-λt} f(ω_t) dt`, as an identity in `[0, ∞]` for nonnegative
  measurable `f` (`Killed/Resolvent.lean`); along an open
  exhaustion the exit times tend to infinity and the killed kernels increase to the transition
  kernels (`Path/Exhaustion.lean`, `Killed/Minimal.lean`).
- **Lifetime paths** (`Lifetime/`): paths with a lifetime and a cemetery state, killing, exit
  times of open sets as stopping times, nonexplosion and the transport to ordinary continuous
  paths.
- **Parameterized families** (`Parameterized/`): the same kernels and dense-time construction
  with joint measurability in an environment parameter, and the **quenched continuous-path
  process** as a single kernel from `Theta × α` to path space, with the exact fibre identity to
  the unparameterized process, the marginals, starting law, Markov and strong Markov properties
  of the single-semigroup process transported to it (`Parameterized/ContinuousProcessProperties.lean`),
  measurable quenched expectations, and the **annealed law** with its expectations as averages
  of the quenched ones (`Parameterized/Annealed.lean`).
- **Equivariance** (`Trajectory/Equivariance.lean`, `Parameterized/Equivariance.lean`): under a
  homeomorphism between two state spaces and a time rescaling, the process of the conjugated semigroup
  is the pushforward of the original process, by uniqueness; covariance of quenched families under
  environment symmetries; the moment criterion transfers under isometries.
- **Examples** (`Examples/`): the identity semigroup and the deterministic drift semigroup
  satisfy every hypothesis of the main theorem, and their processes are identified (the constant
  path, the straight line); the **heat semigroup** on the line satisfies them too, its process is
  **Brownian motion** in the form Mathlib proves equivalent to its definition (Gaussian
  marginals, independent increments, continuous paths), and its generator is half the Laplacian
  on twice continuously differentiable `C₀` functions with `C₀` second derivative
  (`Examples/HeatSemigroup.lean`, `Examples/BrownianMotion.lean`, `Examples/HeatGenerator.lean`).

## From a generator to the process

The library contains no PDE, but it is built to be the probabilistic end of an analytic
pipeline, and the analytic end is where a consumer connects an operator to it:

1. **From a resolvent to a Feller semigroup.** A consumer who can solve the resolvent equation
   `(λ − L) u = f` on `C₀(α)` for an operator `L` satisfying the positive maximum principle
   packages the solution operators as a `PositiveC0ContractiveResolvent α` (the resolvent
   identity, the Hille–Yosida bound, dense range, positivity). The library then produces the
   strongly continuous positive contraction semigroup on `C₀(α)` generated by that resolvent
   (Hille–Yosida through the Yosida approximation, `Semigroup/`), represents it by a jointly
   measurable sub-Markov kernel semigroup (Riesz representation, `Kernel/PositiveC0*`), and
   proves that this kernel semigroup is Feller with the generated semigroup as its `C₀`
   action: `PositiveC0ContractiveResolvent.kernelSemigroup`,
   `isFellerKernelSemigroup_kernelSemigroup`, `integral_kernelSemigroup`.
2. **From the semigroup to the process.** Conservativity and the Kolmogorov moment criterion,
   both statements about the transition kernels only, give the process by the main theorem.
3. **Back to the operator.** The generator of the `C₀` semigroup, defined as the limit of its
   difference quotients, is developed in `Semigroup/Generator.lean`, and Dynkin's formula, the
   Dynkin martingale, the expected exit time bound and the harmonic and Poisson representations
   at truncated exit times (`Trajectory/Dynkin*.lean`, `Trajectory/HarmonicRepresentation.lean`)
   express expectations
   of the process through that generator applied to `f` in its domain. The identification of
   this generator with the operator the consumer supplied is formalized: the resolvent of the
   `C₀` semigroup of the process built from `R` is `R` itself
   (`PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup`), the generator domain
   is the range of `R_λ` with `L (R_λ g) = λ R_λ g − g`
   (`Semigroup/GeneratorResolvent.lean`, `Feller/Resolvent.lean`), and no other strongly
   continuous contraction semigroup has that generator (`Semigroup/GeneratorUniqueness.lean`).
   For an elliptic `L` the killed process (`Killed/`) is then the probabilistic side of the
   Dirichlet problem on the open set, through the harmonic representation and the killed
   resolvent.

The consumer supplies the resolvent of its operator and the two estimates on the transition
kernels; the semigroup, the process, the strong Markov property, the identification of the
generator and Dynkin's formula are in the library. See the consumer guide, sections 9, 10
and 12.

## What is not covered

The library does not construct
càdlàg processes for Feller semigroups without a continuity criterion (jump processes are out of
scope by design), does not augment the filtration (statements are for the raw canonical
filtration), and contains no Dirichlet-form theory, potential theory, generators of specific
operators, or PDE. The Kolmogorov moment criterion is a hypothesis; the library proves nothing
about which semigroups satisfy it beyond the identity, deterministic-drift and heat examples in
`Examples/`.

## Relation to the literature

The main theorem combines three classical ingredients:

- **Existence of a process with prescribed finite-dimensional distributions**: Kolmogorov's
  extension theorem, here in the Markov form due to Ionescu Tulcea (1949).
- **Continuous paths**: the Kolmogorov–Chentsov continuity theorem (Kolmogorov 1934, first
  published by Slutsky 1937; Chentsov 1956), applied to the process on the countable dense time
  set.
- **The strong Markov property of Feller processes**: Dynkin and Yushkevich (1956) and
  Blumenthal (1957).

Textbook treatments of Feller processes, their càdlàg realization, and the strong Markov
property:

- Dynkin, *Markov Processes* (1965).
- Blumenthal and Getoor, *Markov Processes and Potential Theory* (1968).
- Revuz and Yor, *Continuous Martingales and Brownian Motion*, Chapter III.
- Rogers and Williams, *Diffusions, Markov Processes and Martingales*, Volume 1, Chapter III
  (under the name Feller–Dynkin processes).
- Ethier and Kurtz, *Markov Processes: Characterization and Convergence*, Chapter 4.
- Kallenberg, *Foundations of Modern Probability*, the chapter on Feller processes and
  semigroups.
- Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Chapter 6.

The library's statement is the continuous-path case of that theory:

- the Kolmogorov moment criterion replaces the càdlàg realization;
- uniqueness in law is derived from the identification of a law on continuous paths by its
  rational-time marginals;
- the dense-time process is built by Ionescu Tulcea over `ℚ≥0` rather than by the Kolmogorov
  extension theorem over all times;
- the strong Markov property is proved for the raw canonical filtration by approximating a
  stopping time from above with dyadic ceilings, so no augmentation or right-continuity of the
  filtration is needed.

Formalizations this library builds on or is comparable to:

- Mathlib's Markov kernels (Degenne, *Markov kernels in Mathlib's probability library*,
  [arXiv:2510.04070](https://arxiv.org/abs/2510.04070)) and the Ionescu-Tulcea theorem
  (Marion, *A formalization of the Ionescu-Tulcea theorem in Mathlib*,
  [arXiv:2506.18616](https://arxiv.org/abs/2506.18616)), which the dense-time construction
  uses directly.
- The Kolmogorov–Chentsov theorem and the construction of Brownian motion in Lean (Degenne,
  Ledvinka, Marion, Pfaffelhuber, *Formalization of Brownian motion in Lean*,
  [arXiv:2511.20118](https://arxiv.org/abs/2511.20118), being migrated to Mathlib); at the
  pinned Mathlib revision only the `IsKolmogorovProcess` predicate is upstreamed, which this
  library uses, proving its own dyadic chaining argument for the dense-time process of a
  semigroup. The process of the heat semigroup built here is a Brownian motion in the sense of
  that formalization's definition, now Mathlib's `IsBrownianReal`, through the characterization
  by Gaussian marginals and independent increments (`Examples/BrownianMotion.lean`).
- The Isabelle/HOL formalization of the Kolmogorov–Chentsov theorem (Pardillo-Laursen and
  Foster, [Archive of Formal Proofs, 2025](https://isa-afp.org/entries/Kolmogorov_Chentsov.html)),
  and Hölzl's Markov chains, Markov decision processes and Markov processes in Isabelle/HOL
  (Journal of Automated Reasoning 59, 2017; CPP 2017), which construct discrete-time
  trajectory measures via the Giry monad and Ionescu-Tulcea and derive the strong Markov
  property of discrete-time Markov processes.

To the author's knowledge, the existence and uniqueness of a continuous-path strong Markov
process from a Feller transition semigroup, with the strong Markov property at arbitrary finite
stopping times of the raw filtration, had not previously been formalized in a proof assistant.
The closest prior results are Hölzl's strong Markov property for discrete-time Markov processes
in Isabelle/HOL (CPP 2017) and the Markov property of Brownian motion in Lean
(arXiv:2511.20118, where the strong Markov property is listed as future work); the present
library obtains the strong Markov property of Brownian motion as the instance of its general
theorem for the heat semigroup.

## Verified against a Mathlib-only statement

So that the central claim can be checked without trusting the library, the main theorem is
restated using **only Mathlib**, with every definition it needs rebuilt from Mathlib
primitives, in [`Audit/ContinuousMarkovProcess/Challenge.lean`](Audit/ContinuousMarkovProcess/Challenge.lean),
and [`Solution.lean`](Audit/ContinuousMarkovProcess/Solution.lean) proves that exact statement
from the library. The pair is checked by
[`leanprover/comparator`](https://github.com/leanprover/comparator), which confirms that the
two elaborated types are identical constant by constant and that the proof reduces to the three
standard axioms, printing `Your solution is okay!`; see [`Audit/README.md`](Audit/README.md).

Two statements are verified this way. The first is
`MarkovProcessChallenge.existsUnique_continuousMarkovProcess`: for a
sub-Markov kernel semigroup (a five-field structure over Mathlib's `Kernel`), conservative,
Feller (integration against `P t` maps `C₀(α, ℝ)` into itself and the induced contractions have
norm-continuous orbits), and satisfying the Kolmogorov moment criterion, there is exactly one
Markov kernel into `C(NNReal, α)` whose finite-dimensional distributions are the iterated
compositions of the transitions along the increasing enumeration of each finite set of times.
The challenge statement has the same hypotheses as the library's
`existsUnique_continuousProcess_of_hasKolmogorovMoments` (the intrinsic moment criterion); it
differs only in binder order and in rebuilding the vocabulary from Mathlib.

The second is `BrownianMotionChallenge.brownianMotion`
([`Audit/BrownianMotion/Challenge.lean`](Audit/BrownianMotion/Challenge.lean)): there is exactly
one Markov kernel from `ℝ` to `C([0, ∞), ℝ)` with the finite-dimensional distributions of the
Gaussian heat kernels `x ↦ N(x, t)`; under it, from every starting point, the centred canonical
process has Gaussian marginals `N(0, t)`, independent increments and continuous paths, which is
Mathlib's definition of Brownian motion through its characterization theorem; and for every
twice continuously differentiable `f` with `f` and `f''` vanishing at infinity,
`t⁻¹ (P_t f − f) → ½ f''` uniformly as `t → 0⁺`. The solution proves it from
`Examples/HeatSemigroup.lean`, `Examples/BrownianMotion.lean` and `Examples/HeatGenerator.lean`.

## Building

The project uses [`elan`](https://github.com/leanprover/elan) and Lake; the toolchain is pinned
in [`lean-toolchain`](lean-toolchain).

```bash
lake exe cache get   # prebuilt mathlib oleans; avoids a multi-hour mathlib build
lake build
```

`lake exe cache get` requires the committed [`lake-manifest.json`](lake-manifest.json). On an
8-core machine with the cache in place, the library elaborates from scratch in about two
minutes (measured on that machine); no single module takes more than a few seconds.

To use the library, `import MarkovProcess` pulls in everything; `import MarkovProcess.Main`
is the consumer entry point.

Continuous integration rebuilds the whole library on every push to `main` and every pull
request, under the lakefile's lint options and with the consumer-guide probe, checks that the
Lean excerpts in this file and in the guide are verbatim from the source and that the module and
line counts above are current, and a second workflow,
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), re-runs the comparator
check of the main theorem with both the Lean kernel and the independent `nanoda` kernel. The
live status of both is shown in the badges at the top of this file and in the
[Actions tab](https://github.com/scottnarmstrong/MarkovProcess/actions).

## Repository layout

```
MarkovProcess/
  Semigroup/      contraction semigroups on a Banach space, resolvents, Yosida, generation
  Kernel/         sub-Markov kernels, kernel semigroups, C₀ and Lᵖ actions, moment criterion
  Time/           countable dense times, finite ordered time families, grids
  FiniteTime/     finite-dimensional distributions and their algebra
  DenseTime/      the Ionescu-Tulcea dense-time process and its marginals, cemetery extension
  Continuity/     Kolmogorov continuity by dyadic chaining, transport to continuous paths
  Path/           continuous-path space, filtration, shifts, Polish structure, stopping times
  Feller/         the Feller property and its finite-time continuity estimates
  Trajectory/     the continuous-path process and its restart theorems
  Restart/        generic conditional-restart machinery
  Parameterized/  environment-parameterized kernels and dense-time processes
  Lifetime/       paths with lifetime, killing, exit times, nonexplosion
  Killed/         the process killed at the exit of an open set: kernels, semigroup, lifetime-path
                  process, resolvent, exhaustions
  Examples/       the identity and drift semigroups as certificates of the main theorem
  Main.lean       the consumer-facing API and the main theorem
MarkovProcess.lean  root module importing the whole library
Audit/              Mathlib-only comparator challenge and solution
docs/CONVENTIONS.md ambient assumptions, stopping-time conventions, style
docs/CONSUMER_GUIDE.md  fact-to-theorem map with compiled usage examples (docs/ConsumerGuide.lean)
scripts/            gen_modules.py (regenerates MODULES.md), check_docs.sh (compiles the guide),
                    check_readme.py (README and guide excerpts verbatim from the source, counts current),
                    release_check.sh (tracked-tree gate)
```

Contribution rules are in [`CONTRIBUTING.md`](CONTRIBUTING.md).

## How this was built

The Lean code was written by Claude Fable 5.1 (Anthropic) and GPT-5.6-Sol (OpenAI), through
the Claude Code and Codex agentic harnesses, under the close supervision of the author, within
a single week and using only consumer accounts (total spend below 100 USD). Every proof is
checked by the Lean kernel and Mathlib; the main theorem is additionally certified by
`leanprover/comparator` against a Mathlib-only statement, and the public statements were
reviewed by the author. Details are in [`formalization.yaml`](formalization.yaml).

## Authors and citation

The Lean development is by **Scott Armstrong**. If you use this library, please cite it using
the metadata in [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0; see [`LICENSE`](LICENSE).
