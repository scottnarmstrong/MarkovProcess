# Consumer guide

This guide is for a project that imports `MarkovProcess` and wants to *use* the continuous-path
Markov process of a Feller semigroup without reading the construction. Every fact below names
the theorem that delivers it, and every code block in this file compiles against the library
(they are kept verbatim in `docs/ConsumerGuide.lean` and compiled in CI).

Conventions used throughout (details in [`CONVENTIONS.md`](CONVENTIONS.md)):

- times are `NNReal`; a finite stopping time is a map `T : ContinuousPath alpha → NNReal` whose
  coercion to `WithTop NNReal` is a Mathlib `IsStoppingTime` for the canonical filtration
  `ContinuousPath.canonicalFiltration`;
- the stopped sigma-algebra is Mathlib's `IsStoppingTime.measurableSpace`;
- path space `ContinuousPath alpha` is `C(NNReal, alpha)` with the compact-open topology and its
  Borel sigma-algebra (global instances in `Path/Basic.lean`);
- every statement holds for **every** starting point `x`; there are no exceptional null sets.

## 0. Set-up

```lean
import MarkovProcess.Main
import MarkovProcess.Path.ExitTime
import MarkovProcess.Killed.Kernel
import MarkovProcess.Killed.Marginals
import MarkovProcess.Killed.Nested
import MarkovProcess.Trajectory.Dynkin
import MarkovProcess.Trajectory.DynkinStopping
import MarkovProcess.Trajectory.PathModulus
import MarkovProcess.Trajectory.PathTightness
import MarkovProcess.Trajectory.WeakContinuity
import MarkovProcess.Trajectory.StartingPointContinuity
import MarkovProcess.Trajectory.StoppingLtTop
import MarkovProcess.Trajectory.Equivariance
import MarkovProcess.Parameterized.Equivariance
import MarkovProcess.Parameterized.ContinuousProcessProperties
import MarkovProcess.Parameterized.Annealed
import MarkovProcess.Examples.BrownianMotion
import MarkovProcess.Examples.HeatSemigroup
import MarkovProcess.Examples.HeatGenerator
import MarkovProcess.Examples.Identity
import MarkovProcess.Kernel.PositiveC0Resolvent
import MarkovProcess.Semigroup.GeneratorResolvent
import MarkovProcess.Semigroup.GeneratorUniqueness
import MarkovProcess.Semigroup.ResolventGeneration
import MarkovProcess.Feller.Resolvent
import MarkovProcess.Semigroup.TrotterKato
import MarkovProcess.Trajectory.Convergence
import MarkovProcess.Trajectory.WeakConvergence
```

```lean
open MeasureTheory ProbabilityTheory MarkovProcess SubMarkovKernelSemigroup
open scoped BoundedContinuousFunction ENNReal NNReal ZeroAtInfty

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [Nonempty alpha] [MeasurableSpace alpha] [BorelSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
  (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M)
```

The state space is a nonempty locally compact Polish space with its Borel sigma-algebra. The
hypotheses on the semigroup are: conservativity (`P.IsConservative`, every `P t x` a probability
measure), the Feller property (`P.IsFellerKernelSemigroup`: `C₀` is mapped into itself with
norm-continuous orbits), and the intrinsic Kolmogorov moment criterion
`P.HasKolmogorovMoments p q M` (`0 < p`, `1 < q`, `∫ edist z y ^ p ∂(P h y) ≤ M * h ^ q`).

Local compactness and the Feller property are used only to read marginals at irrational times.
Everything with `_denseTime` in its name, and every uniqueness statement, is proved without
them.

## 1. Getting the process

| fact | theorem |
| --- | --- |
| existence and uniqueness, intrinsic hypotheses | `IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments` |
| existence and uniqueness, construction-level regularity | `IsFellerKernelSemigroup.existsUnique_continuousProcess` |
| the canonical object | `IsConservative.continuousProcess P hP : Kernel alpha (ContinuousPath alpha)` |
| it is a Markov kernel | instance `isMarkovKernel_continuousProcess` |
| regularity from the moment criterion | `KolmogorovRegular.of_hasKolmogorovMoments` |

```lean
example : ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
    ∀ I : Finset NNReal, Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I :=
  hFeller.existsUnique_continuousProcess_of_hasKolmogorovMoments P hP hmom

noncomputable example : Kernel alpha (ContinuousPath alpha) :=
  IsConservative.continuousProcess P hP

example : IsMarkovKernel (IsConservative.continuousProcess P hP) := inferInstance

example : P.KolmogorovRegular hP := KolmogorovRegular.of_hasKolmogorovMoments P hP hmom
```

Most property theorems take the regularity certificate `hK : P.KolmogorovRegular hP`; obtain it
once from the moment criterion as in the last line and pass it along.

## 2. Marginals and the starting law

| fact | theorem |
| --- | --- |
| finite-dimensional distributions at all real times | `IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation` |
| the same at rational times, no Feller hypothesis | `IsConservative.continuousProcess_map_finiteEvaluation_denseTime` |
| one-time marginal at a rational time | `IsConservative.continuousProcess_map_eval` |
| starting law: `ω(0)` has law `δₓ` under `Q x` | `IsConservative.continuousProcess_map_eval_zero` |

```lean
example (I : Finset NNReal) :
    (IsConservative.continuousProcess P hP).map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel P I :=
  hFeller.continuousProcess_map_finiteEvaluation P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) I

example : (IsConservative.continuousProcess P hP).map (fun omega ↦ omega 0) = Kernel.id :=
  IsConservative.continuousProcess_map_eval_zero P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)
```

`finiteSetKernel P I x` is the law of `(ω t)_{t ∈ I}` obtained by iterating the transition
kernels along the increasing enumeration of `I`.

### Regularity in the starting point (`Trajectory/StartingPointContinuity.lean`)

| fact | theorem |
| --- | --- |
| expectations `x ↦ ∫ F d(Q x)` are (strongly) measurable | `IsConservative.stronglyMeasurable_integral_continuousProcess`, `measurable_integral_continuousProcess` |
| the same for functionals of the path shifted at, or the state at, a finite stopping time | `IsConservative.measurable_integral_shift_stoppingTime_continuousProcess`, `measurable_integral_eval_stoppingTime_continuousProcess` |
| **weak continuity of the finite-dimensional laws** in the starting point (bounded continuous tests) | `IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel` |
| continuity of cylinder expectations of the process; one-time case | `IsFellerKernelSemigroup.continuous_integral_finsetEvaluation_continuousProcess`, `continuous_integral_eval_continuousProcess` |

```lean
example (t : NNReal) (g : BoundedContinuousFunction alpha ℝ) :
    Continuous fun x ↦ ∫ omega, g (omega t) ∂(IsConservative.continuousProcess P hP x) :=
  hFeller.continuous_integral_eval_continuousProcess P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) t g
```

Weak continuity of the whole path law `x ↦ Q x` on path space is section 13
(`IsFellerKernelSemigroup.continuous_pathLaw`), under a proper state space.

## 3. Markov property at deterministic times

| fact | theorem |
| --- | --- |
| shift identity `Q.map (shift s) = Q ∘ P s` | `IsFellerKernelSemigroup.continuousProcess_map_shift` |
| restart of the law restricted to an `𝓕_s` event | `IsFellerKernelSemigroup.continuousProcess_restrict_map_shift` |
| conditional expectation given `𝓕_s` | `IsFellerKernelSemigroup.continuousProcess_condExp_shift` |

```lean
example (s : NNReal) :
    (IsConservative.continuousProcess P hP).map (ContinuousPath.shift s) =
      (IsConservative.continuousProcess P hP).comp (P s) :=
  hFeller.continuousProcess_map_shift P hP (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) s
```

The conditional-expectation form reads, for bounded strongly measurable `F` into a Banach
space, `E_x[F(ω(s + ·)) | 𝓕_s] = E_{ω(s)}[F]` almost surely under `Q x`.

## 4. Strong Markov property at finite stopping times

| fact | theorem |
| --- | --- |
| restart form, any finite stopping time | `IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime` |
| conditional-expectation form, any finite stopping time | `IsFellerKernelSemigroup.continuousProcess_condExp_shift_stoppingTime` |
| conditional-expectation form, countable range | `IsFellerKernelSemigroup.continuousProcess_condExp_shift_countableStoppingTime` |
| measurability of `ω ↦ ω(T ω)` | `ContinuousPath.measurable_eval_stoppingTime_borel` |

A typical stopping time is the exit time of an open set truncated at a horizon (section 6). With
`T := ContinuousPath.exitTimeTrunc U K` and its stopping-time certificate, the strong Markov
property at `T` is one application:

```lean
example (U : Set alpha) (hU : IsOpen U) (K : NNReal) (x : alpha)
    (F : ContinuousPath alpha → ℝ) (hF : StronglyMeasurable F) (C : ℝ)
    (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((IsConservative.continuousProcess P hP) x)[fun omega ↦
        F (ContinuousPath.shift (ContinuousPath.exitTimeTrunc U K omega) omega) |
        (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K).measurableSpace] =ᵐ[
      (IsConservative.continuousProcess P hP) x]
      fun omega ↦ ∫ eta, F eta ∂(IsConservative.continuousProcess P hP)
        (omega (ContinuousPath.exitTimeTrunc U K omega)) :=
  hFeller.continuousProcess_condExp_shift_stoppingTime P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) x
    (ContinuousPath.exitTimeTrunc U K) (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K)
    F hF C hFC
```

### Stopping times that may be infinite (`Trajectory/StoppingLtTop.lean`)

For a Mathlib stopping time `tau : ContinuousPath alpha → WithTop NNReal` of the canonical
filtration, the finite value is written `(tau omega).untopD 0` and the statements live on the
event `{omega | tau omega < ⊤}`:

| fact | theorem |
| --- | --- |
| restart form on `A ∩ {τ < ⊤}` for an event `A` of the stopped sigma-algebra | `IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top` |
| conditional-expectation form, with the indicator of `{τ < ⊤}` on both sides | `IsFellerKernelSemigroup.continuousProcess_condExp_shift_stoppingTime_lt_top` |
| measurability of `ω ↦ ω ((τ ω).untopD 0)`; `{τ < ⊤}` is in the stopped sigma-algebra | `ContinuousPath.measurable_eval_untopD_stoppingTime`, `StoppingTime.measurableSet_stoppingTime_lt_top` |

Applied to the exit time `exitTimeTop U` of an open set, this is the strong Markov property at the
exit time on the event that the path leaves `U`:

```lean
example (U : Set alpha) (hU : IsOpen U) (x : alpha)
    (F : ContinuousPath alpha → ℝ) (hF : StronglyMeasurable F) (C : ℝ)
    (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((IsConservative.continuousProcess P hP) x)[
        {omega | ContinuousPath.exitTimeTop U omega < ⊤}.indicator fun omega ↦
          F (ContinuousPath.shift ((ContinuousPath.exitTimeTop U omega).untopD 0) omega) |
        (ContinuousPath.isStoppingTime_exitTime U hU).measurableSpace] =ᵐ[
      (IsConservative.continuousProcess P hP) x]
      {omega | ContinuousPath.exitTimeTop U omega < ⊤}.indicator fun omega ↦
        ∫ eta, F eta ∂(IsConservative.continuousProcess P hP)
          (omega ((ContinuousPath.exitTimeTop U omega).untopD 0)) :=
  hFeller.continuousProcess_condExp_shift_stoppingTime_lt_top P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) x (ContinuousPath.exitTimeTop U)
    (ContinuousPath.isStoppingTime_exitTime U hU) F hF C hFC
```

## 5. Uniqueness as an equation

| fact | theorem |
| --- | --- |
| any finite kernel with the marginals of `P` is `continuousProcess P hP` | `IsConservative.eq_continuousProcess_of_map_finiteEvaluation` |
| the same from rational-time marginals only | `IsConservative.eq_continuousProcess_of_map_finiteEvaluation_denseTime` |
| the construction does not depend on its fallback path | `IsConservative.continuousProcess_eq_continuousPathTrajectory` |

```lean
example (Q : Kernel alpha (ContinuousPath alpha)) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) :
    Q = IsConservative.continuousProcess P hP :=
  IsConservative.eq_continuousProcess_of_map_finiteEvaluation P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) Q hQ
```

This is the tool for every covariance or equivariance statement: show that the transported
kernel has the right marginals and conclude that it *is* the process.

## 6. Exit times of open sets

All in `MarkovProcess/Path/ExitTime.lean` (namespace `ContinuousPath`), for an open set `U`.

| fact | theorem |
| --- | --- |
| the exit time `exitTime U ω : ℝ≥0∞` and its `WithTop NNReal` form `exitTimeTop U` | definitions |
| it is a stopping time of the canonical filtration | `isStoppingTime_exitTime` |
| truncation `exitTimeTrunc U K : ContinuousPath alpha → NNReal` is a finite stopping time | `isStoppingTime_exitTimeTrunc` |
| `exitTimeTrunc U K ≤ K`; its value is `min (exitTime U ω) K` | `exitTimeTrunc_le`, `coe_exitTimeTrunc` |
| finite exactly when the path leaves `U` | `exitTime_lt_top_iff`, `exitTime_eq_top_iff` |
| inside `U` strictly before the exit time | `mem_of_lt_exitTime` |
| at a finite exit time the path is on `frontier U`, if it started in `U` | `coordinate_exitTime_mem_frontier` |

Laws at stopping and exit times as kernels (`Trajectory/ExitLaw.lean`, namespace
`SubMarkovKernelSemigroup`):

| fact | theorem |
| --- | --- |
| the **stopped law** `x ↦ law of (T ω, ω (T ω))` for a finite stopping time, a Markov kernel, with its two marginals | `IsConservative.stoppedLaw`, `stoppedLaw_apply`, `stoppedLaw_map_fst`, `stoppedLaw_map_snd` |
| the law of the position at the exit time truncated at `K`; it lives on the closure of `U` from a start in `U` | `IsConservative.exitLawTrunc`, `exitLawTrunc_apply`, `integral_exitLawTrunc`, `exitLawTrunc_apply_compl_closure` |
| the **exit distribution (harmonic measure)** on the event that the path leaves `U`; total mass the exit probability; lives on the frontier from a start in `U` | `IsConservative.exitLaw`, `exitLaw_apply`, `exitLaw_apply_univ`, `exitLaw_apply_compl_frontier` |
| harmonic representation in kernel form: `L f = 0` on `U` ⇒ `∫ f d(exitLawTrunc x) = f x` | `IsFellerKernelSemigroup.integral_exitLawTrunc_eq_of_generator_eq_zero` |

## 7. Measurably parameterized (quenched) families

For a jointly measurable family `Pq : ParameterizedSubMarkovKernelSemigroup Theta alpha` of
semigroups indexed by a measurable parameter space `Theta`, the library builds one kernel from
`Theta × alpha` to path space, so that measurability in the parameter never has to be proved by
hand. All names below live in `ParameterizedSubMarkovKernelSemigroup`.

| fact | theorem |
| --- | --- |
| the quenched process as one kernel | `IsConservative.continuousProcess : Kernel (Theta × alpha) (ContinuousPath alpha)` |
| it is a Markov kernel | instance `isMarkovKernel_continuousProcess` |
| **fibre identity**: at `(θ, x)` it is the process of `Pq θ` started at `x`, exactly | `IsConservative.continuousProcess_apply`, `continuousProcess_apply'` |
| quenched expectations are measurable in `(θ, x)` | `measurable_integral_continuousProcess`, `stronglyMeasurable_integral_continuousProcess` |
| the same for cylinder functionals | `measurable_integral_finsetEvaluation_continuousProcess` |
| fibrewise hypotheses stated once | `IsConservative`, `KolmogorovRegular`, `HasKolmogorovMoments` (all fibrewise) |
| every property of sections 2 to 4 at `(θ, x)` (`Parameterized/ContinuousProcessProperties.lean`) | `IsConservative.continuousProcess_map_eval[_zero]`, `_map_finiteEvaluation[_denseTime]`, `_map_shift`, `_restrict_map_shift[_stoppingTime]`, `_condExp_shift[_stoppingTime\|_countableStoppingTime]` |
| kernel form of the starting law | `IsConservative.continuousProcess_map_eval_zero'` |
| **annealed law** `∫ Q(θ, x) μ(dθ)` as a kernel (`Parameterized/Annealed.lean`) | `IsConservative.annealedProcess`, `annealedProcess_apply` |
| annealed expectations are averages of quenched ones | `IsConservative.integral_annealedProcess`, `lintegral_annealedProcess` |
| annealed marginals and starting law | `IsConservative.annealedProcess_map_finiteEvaluation_apply`, `annealedProcess_map_eval_zero` |
| **killed parameterized family** on the carrier `U`, with fibres the killed semigroups (`Parameterized/Killed.lean`) | `IsConservative.killedFamily`, `killedFamily_toSubMarkovKernelSemigroup`, `killedFamily_apply`, `measurable_killedKernelOn_family` |

```lean
section Quenched
variable {Theta : Type*} [MeasurableSpace Theta]
variable (Pq : ParameterizedSubMarkovKernelSemigroup Theta alpha) (hPq : Pq.IsConservative)
  (hFellerq : ∀ theta, (Pq.toSubMarkovKernelSemigroup theta).IsFellerKernelSemigroup)
  (hKq : Pq.KolmogorovRegular hPq)

noncomputable example : Kernel (Theta × alpha) (ContinuousPath alpha) :=
  ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess Pq hPq

example (theta : Theta) (x : alpha) :
    ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess Pq hPq (theta, x) =
      IsConservative.continuousProcess (Pq.toSubMarkovKernelSemigroup theta) (hPq theta) x :=
  ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_apply Pq hPq theta x

example (F : ContinuousPath alpha → ℝ) (hF : StronglyMeasurable F) :
    Measurable fun p : Theta × alpha ↦
      ∫ eta, F eta
        ∂ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess Pq hPq p :=
  ParameterizedSubMarkovKernelSemigroup.measurable_integral_continuousProcess Pq hPq F hF

-- strong Markov property of the quenched process, with the parameter carried along
example (theta : Theta) (x : alpha) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (F : ContinuousPath alpha → ℝ) (hF : StronglyMeasurable F) (C : ℝ)
    (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess Pq hPq (theta, x))[
        fun omega ↦ F (ContinuousPath.shift (T omega) omega) | hT.measurableSpace]
      =ᵐ[ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess Pq hPq (theta, x)]
      fun omega ↦ ∫ eta, F eta
        ∂ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess Pq hPq
          (theta, omega (T omega)) :=
  ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_condExp_shift_stoppingTime
    Pq hPq hFellerq hKq theta x T hT F hF C hFC

-- annealed expectations are averages of quenched expectations
example (mu : Measure Theta) [IsProbabilityMeasure mu] (x : alpha)
    (F : ContinuousPath alpha → ℝ) (hF : StronglyMeasurable F) (C : ℝ)
    (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ∫ omega, F omega
        ∂(ParameterizedSubMarkovKernelSemigroup.IsConservative.annealedProcess Pq hPq mu x) =
      ∫ theta, ∫ omega, F omega
        ∂(ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess Pq hPq (theta, x))
        ∂mu :=
  ParameterizedSubMarkovKernelSemigroup.IsConservative.integral_annealedProcess Pq hPq mu x F hF
    C hFC
end Quenched
```

The fibre identity is exact, for every parameter and every starting point; the transported
statements never mention it.

## 8. Examples as certificates

`MarkovProcess/Examples/Identity.lean`, `MarkovProcess/Examples/Drift.lean` and
`MarkovProcess/Examples/HeatSemigroup.lean` show that the hypotheses of the main theorem are
jointly satisfiable and identify the resulting processes.

| semigroup | main theorem applied | the process identified |
| --- | --- | --- |
| identity, `idSemigroup t = Kernel.id` | `existsUnique_continuousProcess_idSemigroup` | `continuousProcess_idSemigroup_eq`: the Dirac mass at the constant path |
| drift, `driftSemigroup v t x = δ_{x + t v}` on a finite-dimensional normed space | `existsUnique_continuousProcess_driftSemigroup` | `continuousProcess_driftSemigroup_eq`: the Dirac mass at `driftPath v x` |
| heat, `heatSemigroup t x = gaussianReal x t` on the line | `existsUnique_continuousProcess_heatSemigroup` | `brownianMotion`, with marginals `brownianMotion_map_eval` and `brownianMotion_map_finsetEvaluation`, identified as a Brownian motion by `isBrownianReal_brownianMotion` |

```lean
example (x : alpha) :
    IsConservative.continuousProcess (idSemigroup (alpha := alpha)) isConservative_idSemigroup x =
      Measure.dirac (ContinuousMap.const NNReal x) :=
  continuousProcess_idSemigroup_eq x
```

The heat semigroup is the one instance whose process actually diffuses: it is Feller
(`isFellerKernelSemigroup_heatSemigroup`) and satisfies the Kolmogorov moment criterion with
`p = 4`, `q = 2` (`hasKolmogorovMoments_heatSemigroup`), and its process is Brownian motion.

```lean
example (t : NNReal) (x : ℝ) :
    (brownianMotion x).map (fun omega ↦ omega t) = gaussianReal x t :=
  brownianMotion_map_eval t x
```

`MarkovProcess/Examples/BrownianMotion.lean` identifies that process: recentred at its starting
point, the canonical process has centred Gaussian marginals, independent increments over the
consecutive intervals of every finite monotone family of times
(`hasIndepIncrements_brownianMotion`), and continuous trajectories.  The engine is the simple
Markov property in joint-law form, `brownianMotion_map_prodMk_shift`.

```lean
example (x : ℝ) :
    IsBrownianReal (fun (t : NNReal) (omega : ContinuousPath ℝ) ↦ omega t - x)
      (brownianMotion x) :=
  isBrownianReal_brownianMotion x
```

`MarkovProcess/Examples/HeatGenerator.lean` is a certificate of a different kind: an analytic
identification of the infinitesimal generator of the Gaussian averages
`x ↦ ∫ f d gaussianReal x t` on the line, which is half the second derivative — half the
Laplacian in one dimension. It is stated first for the explicit Gaussian integrals and then in
the `C₀` norm.

| fact | theorem |
| --- | --- |
| second-order Taylor estimate with a modulus: the Taylor polynomial of `f` at `x` approximates `f (x + h)` to within `C h²` as soon as the increment of `f''` over the segment is at most `C` | `abs_sub_taylor_two_le` |
| `t⁻¹ (∫ f d gaussianReal x t - f x)` tends to `f'' x / 2` as `t → 0⁺`, uniformly in the centre `x` | `tendstoUniformly_gaussianAverage_sub_div` |
| the Gaussian average of a `C₀` function is again a `C₀` function, and the same limit holds in the `C₀` norm | `gaussianAverage`, `tendsto_gaussianAverage_sub_div` |
| the `C₀` semigroup of the heat semigroup acts by Gaussian averages; twice continuously differentiable `C₀` functions with `C₀` second derivative lie in its generator domain, where **the generator is half the second derivative** | `c0Semigroup_heatSemigroup_apply`, `mem_generatorDomain_heatSemigroup`, `generator_heatSemigroup` |

```lean
example {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hf0 : Filter.Tendsto f (Filter.cocompact ℝ) (nhds 0))
    (hf2 : Filter.Tendsto (iteratedDeriv 2 f) (Filter.cocompact ℝ) (nhds 0)) :
    TendstoUniformly
      (fun (t : NNReal) (x : ℝ) ↦ (t : ℝ)⁻¹ * (∫ y, f y ∂gaussianReal x t - f x))
      (fun x ↦ iteratedDeriv 2 f x / 2) (nhdsWithin 0 (Set.Ioi 0)) :=
  tendstoUniformly_gaussianAverage_sub_div hf hf0 hf2

example (f g : C₀(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    (hg : ∀ x, g x = iteratedDeriv 2 (f : ℝ → ℝ) x) :
    isFellerKernelSemigroup_heatSemigroup.c0Semigroup.generator
      ⟨f, mem_generatorDomain_heatSemigroup f g hf hg⟩ = (2 : ℝ)⁻¹ • g :=
  generator_heatSemigroup f g hf hg
```

## 9. Generator and Dynkin's formula

`Semigroup/Generator.lean` treats an abstract strongly continuous contraction semigroup
`S : Semigroup.StronglyContinuousContractionSemigroup E`; `Trajectory/Dynkin.lean` applies it to
the `C₀` semigroup `hFeller.c0Semigroup` of a Feller semigroup.

| fact | theorem |
| --- | --- |
| generator domain (a submodule) and generator (a linear map on it) | `S.generatorDomain`, `S.generator`, `tendsto_generator`, `generator_eq_of_tendsto` |
| domain invariant under `S t`; `S t` commutes with the generator | `operator_mem_generatorDomain`, `generator_operator` |
| orbits are right differentiable with derivative `S t (L f)` | `tendsto_differenceQuotient_add`, `hasDerivWithinAt_Ioi` |
| fundamental identity `S t f - f = ∫₀ᵗ S s (L f) ds` | `operator_sub_eq_integral` |
| orbit integrals lie in the domain, `L (∫₀ᵗ S s f ds) = S t f - f`; the domain is dense | `orbitIntegral_mem_generatorDomain`, `generator_orbitIntegral`, `dense_generatorDomain` |
| `(S t f) x = E_x f(ω_t)` for the `C₀` semigroup of a Feller semigroup | `IsFellerKernelSemigroup.c0Semigroup_apply_eq_integral` |
| one-time marginal at every real time | `IsFellerKernelSemigroup.continuousProcess_map_eval_nnreal` |
| **Dynkin's formula** `E_x f(ω_t) - f x = E_x ∫₀ᵗ (L f)(ω_s) ds` | `IsFellerKernelSemigroup.integral_eval_sub_eq_integral_integral_generator` |
| the **Dynkin process** `M_t = f(ω_t) - ∫₀ᵗ (L f)(ω_s) ds` and its bound, adaptedness, continuity in time | `IsFellerKernelSemigroup.dynkinProcess`, `norm_dynkinProcess_le`, `adapted_dynkinProcess`, `continuous_dynkinProcess` (`Trajectory/DynkinMartingale.lean`) |
| **the Dynkin process is a martingale** for the canonical filtration under `Q x`, every `x` | `IsFellerKernelSemigroup.martingale_dynkinProcess` |
| **optional stopping in continuous time** (any filtration indexed by `ℝ≥0`; locally bounded, right-continuous martingale; bounded finite stopping time) | `MarkovProcess.integral_stoppedValue_eq_of_locallyBounded`, `integral_stoppedValue_eq_of_le` (`Path/OptionalStopping.lean`) |
| **Dynkin's formula at a bounded stopping time** `E_x f(ω_T) - f x = E_x ∫₀ᵀ (L f)(ω_s) ds` | `IsFellerKernelSemigroup.integral_eval_stoppingTime_sub_eq_integral_integral_generator`, `integral_dynkinProcess_stoppingTime` (`Trajectory/DynkinStopping.lean`) |
| **expected exit time bound**: `L f ≤ -1` on `U`, `m ≤ f` ⇒ `E_x[τ_U ∧ K] ≤ f x - m`, uniformly in `K` | `IsFellerKernelSemigroup.integral_exitTimeTrunc_le` |
| **the expected exit time itself**: `E_x τ_U ≤ f x - m` in `ℝ≥0∞`, hence `τ_U < ∞` almost surely from every `x` | `IsFellerKernelSemigroup.lintegral_exitTime_le`, `ae_exitTime_lt_top` (`Trajectory/ExpectedExitTime.lean`) |
| **harmonic representation** `L f = 0` on `U` ⇒ `E_x f(ω_{τ∧K}) = f x`; **Poisson representation** `L f = -g` on `U` ⇒ `E_x f(ω_{τ∧K}) + E_x ∫_0^{τ∧K} g(ω_s) ds = f x` | `IsFellerKernelSemigroup.integral_eval_exitTimeTrunc_eq_of_generator_eq_zero`, `integral_eval_exitTimeTrunc_add_eq_of_generator_eq_neg` (`Trajectory/HarmonicRepresentation.lean`) |
| **localized Dynkin formula**: for `x ∈ U` and `φ = f` on the closure of `U`, Dynkin at `τ∧K` holds for `φ` with `L f` | `IsFellerKernelSemigroup.integral_eval_exitTimeTrunc_sub_eq_of_eqOn_closure`; the stopped position lies in the closure of `U`: `ContinuousPath.stopped_exitTimeTrunc_mem_closure` |
| the truncated exit time is the generic truncation of `exitTimeTop`; truncations increase to the exit time | `ContinuousPath.exitTimeTrunc_eq_truncTime`, `iSup_exitTimeTrunc` |

```lean
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (S : Semigroup.StronglyContinuousContractionSemigroup E) (f : S.generatorDomain) (t : NNReal) :
    S t f - f = ∫ s in (0 : ℝ)..t, S (Real.toNNReal s) (S.generator f) :=
  S.operator_sub_eq_integral f t

example (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) (x : alpha) :
    ∫ omega, (f : C₀(alpha, ℝ)) (omega t) ∂(IsConservative.continuousProcess P hP x) -
        (f : C₀(alpha, ℝ)) x =
      ∫ omega, (∫ s in (0 : ℝ)..t, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
        ∂(IsConservative.continuousProcess P hP x) :=
  hFeller.integral_eval_sub_eq_integral_integral_generator P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) f t x

example (f : hFeller.c0Semigroup.generatorDomain) (x : alpha) :
    Martingale (hFeller.dynkinProcess f) (ContinuousPath.canonicalFiltration (alpha := alpha))
      (IsConservative.continuousProcess P hP x) :=
  hFeller.martingale_dynkinProcess hP (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) f x

example (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y ≤ -1) {m : ℝ}
    (hm : ∀ y, m ≤ (f : C₀(alpha, ℝ)) y) (K : NNReal) (x : alpha) :
    ∫ omega, (ContinuousPath.exitTimeTrunc U K omega : ℝ)
        ∂(IsConservative.continuousProcess P hP x) ≤ (f : C₀(alpha, ℝ)) x - m :=
  hFeller.integral_exitTimeTrunc_le hP (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) f U hU
    hLf hm K x
```

## 10. The process killed at the exit of an open set

`Killed/Kernel.lean`, for an open set `U` with `hU : IsOpen U`. The killed kernel at time `t` is
`killedKernel P hP U hU t x B = Q x {ω | t < τ_U(ω) ∧ ω t ∈ B}` for measurable `B`.

| fact | theorem |
| --- | --- |
| the killed kernels and their value on a measurable set | `IsConservative.killedKernel`, `killedKernel_apply`, `killedKernel_eq_map` |
| total mass is the survival probability; sub-Markov | `killedKernel_apply_univ`, `isSubMarkovKernel_killedKernel` |
| jointly measurable in `(t, x)` | `measurable_killedKernel` |
| zero off `U`; identity restricted to `U` at time zero | `killedKernel_apply_of_notMem`, `killedKernel_zero` |
| **Chapman–Kolmogorov** `killedKernel (s + t) = killedKernel t ∘ₖ killedKernel s` | `killedKernel_add` |
| path-space identities: `τ(θ_t ω) + t = τ(ω)`, `{s + t < τ} = {s < τ} ∩ {t < τ ∘ θ_s}`, `0 < τ ↔ ω 0 ∈ U` | `ContinuousPath.exitTime_shift_add`, `coe_add_lt_exitTime_iff`, `exitTime_pos_iff` (`Path/ExitTimeShift.lean`, `Killed/Kernel.lean`) |
| survival events measurable; the exit time is Borel | `measurableSet_lt_exitTime_canonicalFiltration`, `measurableSet_lt_exitTime`, `measurable_exitTime` |

On the carrier `alpha` the killed family is not a `SubMarkovKernelSemigroup` (at time zero it is
the identity only on `U`). On the carrier `U` it is one (`Killed/Semigroup.lean`):

| fact | theorem |
| --- | --- |
| the killed kernels on the subtype `U`, their value, and their pushforward to `alpha` | `IsConservative.killedKernelOn`, `killedKernelOn_apply`, `killedKernelOn_apply_eq_continuousProcess`, `map_val_killedKernelOn` |
| no mass leaves `U` | `killedKernel_apply_compl`, `ae_mem_killedKernel` |
| **the killed semigroup** `SubMarkovKernelSemigroup U` and its transition probabilities | `IsConservative.killedSemigroup`, `killedSemigroup_apply`, `killedSemigroup_apply_apply` |
| exit times are monotone in the set; along an **open exhaustion** `U n ↑ α` the exit times of every continuous path tend to infinity (`Path/Exhaustion.lean`) | `ContinuousPath.exitTime_mono`, `IsOpenExhaustion`, `IsOpenExhaustion.tendsto_exitTime_atTop`, `exists_lt_exitTime`, `iSup_exitTime` |
| **the semigroup is the limit of its killed parts**: along an open exhaustion the killed kernels increase to `P t x B`, and the survival probabilities to one (`Killed/Minimal.lean`) | `IsFellerKernelSemigroup.iSup_killedKernel_apply`, `IsConservative.iSup_measure_lt_exitTime`, `killedKernel_mono` |
| the **killed resolvent** `∫_0^∞ e^{-λt} (∫ f d killedKernel_t x) dt = E_x ∫_0^{τ_U} e^{-λt} f(ω_t) dt`, for nonnegative extended measurable `f` (`Killed/Resolvent.lean`) | `IsConservative.killedResolvent`, `killedResolvent_eq_lintegral`, `lintegral_killedKernel` |

The killed process itself lives on lifetime paths (`Path/LifetimePath.lean`): a path with a
lifetime and coordinates in the cemetery extension `Cemetery U` of the carrier
(`Killed/KillAtExit.lean`, `Killed/Process.lean`, `Killed/Marginals.lean`, `Killed/Nested.lean`):

| fact | theorem |
| --- | --- |
| killing a continuous path at its exit time: `killAtExit U ω : LifetimePath U`, its lifetime, coordinates, the shift identity, measurability | `ContinuousPath.killAtExit`, `lifetime_killAtExit`, `coordinate_killAtExit`, `coordinate_killAtExit_shift`, `measurable_killAtExit` |
| **the killed process** `killedProcess P hP U hU : Kernel U (LifetimePath U)`, a Markov kernel; its lifetime is the exit time | `IsConservative.killedProcess`, `killedProcess_apply`, `killedProcess_eq_map`, `killedProcess_map_lifetime` |
| one-time marginal: the cemetery extension of the killed kernel on `U` | `IsConservative.killedProcess_map_coordinate` |
| **finite-dimensional distributions**: those of the cemetery extension of the killed semigroup | `IsConservative.killedProcess_map_finiteEvaluation`, `killedProcess_map_coordinates_ordered` |
| the restart identity on the survival event, a form of the Markov property at a fixed time on an `𝓕_t`-event | `IsConservative.continuousProcess_killedEvent_inter_shift` |
| **nested domains** `U ⊆ V`: the `V`-killed path killed again at the exit of `U` is the `U`-killed path, read through the inclusion; the same for the laws (part-process property) | `ContinuousPath.killedCoordinate_killAtExit`, `lifetimePath_exitTime_killAtExit`, `IsConservative.killedProcess_map_exitTime`, `killedProcess_map_killedCoordinates`, `killedProcess_map_killedFinsetCoordinates` |

The two killed processes of nested domains live on different carriers (`U` and `V`), and the
part-process property compares them through the inclusion of `U` in `V`.

```lean
example (U : Set alpha) (hU : IsOpen U) (I : Finset NNReal) (x : U) :
    (IsConservative.killedProcess P hP U hU x).map
        (fun omega ↦ fun i : I ↦ LifetimePath.coordinate (i : NNReal) omega) =
      finiteSetKernel (cemeterySemigroup (IsConservative.killedSemigroup P hP U hU hFeller
        (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom))) I (Cemetery.alive x) :=
  IsConservative.killedProcess_map_finiteEvaluation P hP U hU hFeller
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) I x

example (U : Set alpha) (hU : IsOpen U) (s t : NNReal) :
    IsConservative.killedKernel P hP U hU (s + t) =
      (IsConservative.killedKernel P hP U hU t).comp (IsConservative.killedKernel P hP U hU s) :=
  IsConservative.killedKernel_add P hP U hU hFeller
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) s t

example (U : Set alpha) (hU : IsOpen U) (t : NNReal) (x : alpha) {B : Set alpha}
    (hB : MeasurableSet B) :
    IsConservative.killedKernel P hP U hU t x B =
      IsConservative.continuousProcess P hP x (ContinuousPath.killedEvent U t B) :=
  IsConservative.killedKernel_apply P hP U hU t x hB
```

## 11. Equivariance and scaling

`Trajectory/Equivariance.lean` (single semigroup) and `Parameterized/Equivariance.lean` (quenched
families), all proved through the uniqueness theorem. For a homeomorphism `e : alpha ≃ₜ beta`
between two state spaces (the same space is allowed) and a time factor `c > 0`, a semigroup `P'`
on `beta` is the *rescaled conjugate* of `P` on `alpha` when
`P' t x = ((P (c * t)) (e.symm x)).map e` (`SubMarkovKernelSemigroup.IsRescaledConjugate P P' e c`);
the path map is `ContinuousPath.rescale e c ω = fun t ↦ e (ω (c * t))`, from paths in `alpha` to
paths in `beta`. Only `P` needs the Feller property; `beta` carries the same standing instances
as `alpha` except local compactness.

| fact | theorem |
| --- | --- |
| the process of `P'` on `beta` is the process of `P` on `alpha` started at `e.symm x`, pushed forward by `rescale e c` | `IsConservative.continuousProcess_eq_map_rescale`, `continuousProcess_apply_rescale` |
| the same with only the moment criterion on `P`, when `e` is an isometry | `IsConservative.continuousProcess_eq_map_rescale_of_hasKolmogorovMoments` |
| pure time rescaling `P' t = P (c t)`; pure conjugation (both on one state space) | `IsConservative.continuousProcess_eq_map_timeRescale`, `continuousProcess_eq_map_conjugate` |
| transfer of the moment criterion under an isometry (constant `M * c ^ q`) | `IsRescaledConjugate.hasKolmogorovMoments` |
| finite-dimensional distributions at arbitrary strictly increasing times | `IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered` |
| finite-dimensional transfer under conjugation and rescaling | `IsRescaledConjugate.finiteTimeKernel_eq`, `finiteSetKernel_eq` (`FiniteTime/KernelEquivariance.lean`) |
| quenched version, with a measurable reparameterization `g` of the environment | `ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale`, `continuousProcess_apply_rescale` |
| **covariance of a quenched family under an environment symmetry** (`P' = P`) | `ParameterizedSubMarkovKernelSemigroup.IsConservative.continuousProcess_covariant` |

Stationarity and re-gauging covariance of a random-environment process are instances of the last
row (`g` the environment shift, `e` the spatial translation, `c = 1`), and diffusive scaling is
the case `e = scaling by λ`, `c = λ²`.

```lean
section Equivariance
variable (P' : SubMarkovKernelSemigroup alpha) (hP' : P'.IsConservative)

example {e : alpha ≃ₜ alpha} (he : Isometry (e : alpha → alpha)) {c : NNReal} (hc : 0 < c)
    (h : P.IsRescaledConjugate P' e c) :
    IsConservative.continuousProcess P' hP' =
      (Kernel.comap (IsConservative.continuousProcess P hP) e.symm e.symm.measurable).map
        (ContinuousPath.rescale e c) :=
  IsConservative.continuousProcess_eq_map_rescale_of_hasKolmogorovMoments P hP P' hP' hFeller hmom
    he hc h
end Equivariance
```

## 12. Starting from a resolvent

`Kernel/PositiveC0Resolvent.lean`: a `PositiveC0ContractiveResolvent alpha` (the resolvent
identity, the Hille–Yosida bound, dense range, and positivity of the shifted resolvents on
`C₀(alpha, ℝ)`) generates a Feller kernel semigroup; the rest of the library applies to it.

| fact | theorem |
| --- | --- |
| the kernel semigroup generated by a positive contractive resolvent | `PositiveC0ContractiveResolvent.kernelSemigroup` |
| it is Feller, and its `C₀` action is the generated semigroup | `isFellerKernelSemigroup_kernelSemigroup`, `integral_kernelSemigroup`, `c0Semigroup_kernelSemigroup` |
| **the generator of the generated semigroup is the operator whose resolvent is `R`**: `L (R_μ g) = μ R_μ g − g`, `R_μ (μ f − L f) = f`, domain `= range R_μ` | `ContractiveResolvent.generator_operator_apply`, `operator_smul_sub_generator`, `generatorDomain_eq_range` (`Semigroup/GeneratorResolvent.lean`) |
| orbits of domain elements are differentiable at every positive time | `StronglyContinuousContractionSemigroup.hasDerivAt_operator_toNNReal` (`Semigroup/Generator.lean`) |
| `μ − L` is injective for `μ > 0`; **the generator determines the semigroup** | `StronglyContinuousContractionSemigroup.eq_of_smul_sub_generator_eq`, `ext_of_generator` (`Semigroup/GeneratorInjectivity.lean`, `Semigroup/GeneratorUniqueness.lean`) |
| the resolvent of any strongly continuous contraction semigroup, `R_μ x = ∫₀^∞ e^{-μt} S_t x dt`: `‖R_μ‖ ≤ μ⁻¹`, `R_μ (μ f − L f) = f`, `L (R_μ x) = μ R_μ x − x`, domain `= range R_μ`, the resolvent identity | `StronglyContinuousContractionSemigroup.resolvent`, `opNorm_resolvent_le`, `resolvent_smul_sub_generator`, `generator_resolvent`, `generatorDomain_eq_range_resolvent`, `resolvent_sub_resolvent` (`Semigroup/Resolvent.lean`) |
| **both Hille–Yosida round trips**: the semigroup generated by the resolvent of `S` is `S`; the resolvent of the semigroup generated by `R` is `R` | `StronglyContinuousContractionSemigroup.generatedSemigroup_toContractiveResolvent`, `ContractiveResolvent.resolvent_generatedSemigroup` (`Semigroup/ResolventGeneration.lean`) |
| the generator is closed | `StronglyContinuousContractionSemigroup.mem_generatorDomain_of_tendsto_generator`, `generator_eq_of_tendsto_generator` (`Semigroup/GeneratorClosed.lean`) |
| the resolvent of the `C₀` semigroup of a Feller kernel semigroup, evaluated: `R_μ f (x) = ∫₀^∞ e^{-μt} P_t f (x) dt`; its generator domain is the range of the resolvent | `IsFellerKernelSemigroup.resolvent_apply_apply`, `mem_generatorDomain_iff_exists_resolvent` (`Feller/Resolvent.lean`) |
| the resolvent of the process built from `R` is `R` | `PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup` |

```lean
section Resolvent
variable (R : PositiveC0ContractiveResolvent alpha)

example : R.kernelSemigroup.IsFellerKernelSemigroup := R.isFellerKernelSemigroup_kernelSemigroup

example (t : NNReal) (f : C₀(alpha, ℝ)) (x : alpha) :
    ∫ y, f y ∂R.kernelSemigroup t x = R.toContractiveResolvent.generatedSemigroup t f x :=
  R.integral_kernelSemigroup t f x

example (hR : R.kernelSemigroup.IsConservative) {p q : ℝ} {M : ℝ≥0}
    (hmomR : R.kernelSemigroup.HasKolmogorovMoments p q M) :
    ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal,
        Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel R.kernelSemigroup I :=
  R.isFellerKernelSemigroup_kernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
    R.kernelSemigroup hR hmomR

example (μ : Semigroup.PositiveShift) (g : C₀(alpha, ℝ)) :
    R.toContractiveResolvent.generatedSemigroup.generator
      ⟨R.toContractiveResolvent.operator μ g,
        R.toContractiveResolvent.operator_mem_generatorDomain μ g⟩ =
      (μ : ℝ) • R.toContractiveResolvent.operator μ g - g :=
  R.toContractiveResolvent.generator_operator_apply μ g

example (μ : Semigroup.PositiveShift) :
    (R.toContractiveResolvent.generatedSemigroup.generatorDomain : Set C₀(alpha, ℝ)) =
      Set.range (R.toContractiveResolvent.operator μ) :=
  R.toContractiveResolvent.generatorDomain_eq_range μ

example (S T : Semigroup.StronglyContinuousContractionSemigroup C₀(alpha, ℝ))
    (hdom : S.generatorDomain = T.generatorDomain)
    (hgen : ∀ (f : C₀(alpha, ℝ)) (hS : f ∈ S.generatorDomain) (hT : f ∈ T.generatorDomain),
      S.generator ⟨f, hS⟩ = T.generator ⟨f, hT⟩) :
    S = T :=
  S.ext_of_generator T hdom hgen

example (μ : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha) :
    hFeller.c0Semigroup.resolvent μ f x =
      ∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-(μ : ℝ) * t) * kernelIntegral (P (Real.toNNReal t)) f x :=
  hFeller.resolvent_apply_apply μ f x

example (μ : Semigroup.PositiveShift) :
    R.isFellerKernelSemigroup_kernelSemigroup.c0Semigroup.resolvent μ =
      R.toContractiveResolvent.operator μ :=
  R.resolvent_c0Semigroup_kernelSemigroup μ
end Resolvent
```

Conservativity and the moment criterion are statements about the transition kernels, which the
consumer proves from its operator; the library takes them as hypotheses. The generator
identification closes the loop from an operator to its process: a consumer who exhibits the
resolvent of its operator `L` as a positive contractive resolvent obtains a Feller semigroup whose
`C₀` generator is `L` on the range of the resolvent, and no other strongly continuous contraction
semigroup has that generator.

## 13. Tightness and weak continuity of the path law

`Trajectory/PathModulus.lean` turns the intrinsic moment criterion into a modulus of continuity
that is uniform in the starting point: the coordinate process of `Q x` is a Kolmogorov process
with the very exponents and constant of `HasKolmogorovMoments`, at *all* nonnegative real times,
and the resulting scale `delta` in the oscillation estimate does not depend on `x`.
`ContinuousPath.modulusSet T delta r` is the closed set of paths whose oscillation over `[0, T]`
at scale `delta` is at most `r`.

| fact | theorem |
| --- | --- |
| the path process is a Kolmogorov process at all real times | `IsConservative.isKolmogorovProcess_continuousProcess` |
| its dense-time projection is the dense-time trajectory | `IsConservative.map_denseRestriction_continuousProcess` |
| modulus of continuity, one scale for every starting point | `IsConservative.exists_measure_compl_modulusSet_le` |
| the modulus set is closed, hence measurable | `ContinuousPath.isClosed_modulusSet`, `measurableSet_modulusSet` |

```lean
example (T : NNReal) {r eps : ℝ≥0∞} (hr : 0 < r) (heps : 0 < eps) :
    ∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ x : alpha,
      IsConservative.continuousProcess P hP x (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps :=
  IsConservative.exists_measure_compl_modulusSet_le P hP hmom T hr heps
```

`Trajectory/PathTightness.lean` turns that estimate into tightness on path space. It asks for a
**proper** state space (closed balls compact); this is what supplies the compact containment
condition, which no modulus can supply on a general Polish space. On a general Polish space
`ContinuousPath.isCompact_moduliSet_of_forall_isCompact` still gives the compact sets of paths
from a compact containment hypothesis, but the tightness theorems below are stated for proper
spaces only. Tightness is asserted for starting points ranging over a compact set: over all
starting points at once it already fails at time zero, where the laws are the Dirac measures.

| fact | theorem |
| --- | --- |
| the path laws over a compact set of starting points are tight | `IsConservative.isTightMeasureSet_continuousProcess` |
| epsilon form: one compact set of paths for all those starting points | `IsConservative.exists_isCompact_measure_compl_le` |
| compact sets of paths from a modulus (Arzelà–Ascoli) | `ContinuousPath.isCompact_moduliSet`, `isCompact_moduliSet_of_forall_isCompact` |

```lean
section Tightness
variable [ProperSpace alpha]

example {K0 : Set alpha} (hK0 : IsCompact K0) :
    IsTightMeasureSet ((fun x ↦ IsConservative.continuousProcess P hP x) '' K0) :=
  IsConservative.isTightMeasureSet_continuousProcess P hP hmom hK0
end Tightness
```

`Trajectory/WeakContinuity.lean` upgrades the cylinder continuity of section 2 to every bounded
continuous functional of the path: the expectation `x ↦ ∫ F d(Q x)` is continuous for every
`F : ContinuousPath alpha →ᵇ ℝ`, and the map `x ↦ Q x` is continuous into the probability
measures on path space with their topology of convergence in distribution. The proof combines
tightness with Stone–Weierstrass on a compact set of paths; no compactness theorem for measures
is used.

| fact | theorem |
| --- | --- |
| weak continuity of the path law in the starting point | `IsFellerKernelSemigroup.continuous_integral_continuousProcess` |
| the same, into `ProbabilityMeasure (ContinuousPath alpha)` | `IsConservative.pathLaw`, `IsFellerKernelSemigroup.continuous_pathLaw` |
| cylinder functionals of the path, and their density | `ContinuousPath.IsBoundedCylinder`, `ContinuousPath.exists_boundedCylinder_approx` |

```lean
section WeakContinuity
variable [ProperSpace alpha]

example (F : ContinuousPath alpha →ᵇ ℝ) :
    Continuous fun x ↦ ∫ omega, F omega ∂(IsConservative.continuousProcess P hP x) :=
  hFeller.continuous_integral_continuousProcess P hP hmom F

example : Continuous (IsConservative.pathLaw P hP) :=
  hFeller.continuous_pathLaw P hP hmom
end WeakContinuity
```

## 14. Convergence of semigroups and processes

Trotter--Kato in `C₀`: for a sequence of Feller semigroups whose resolvents converge strongly at
**one** positive shift, the `C₀` semigroups converge strongly, uniformly on every bounded interval
of times (`tendstoUniformlyOn_operator_of_tendsto_resolvent`, and the pointwise form
`tendsto_operator_of_tendsto_resolvent`). Conversely, strong convergence of the semigroups gives
strong convergence of the resolvents at every positive shift
(`tendsto_resolvent_of_tendsto_operator`); the converse reads a limit under an integral, so it
asks for a countably generated index filter, which `atTop` on `ℕ` is.

```lean
section Convergence
variable (Pn : ℕ → SubMarkovKernelSemigroup alpha)
  (hFellern : ∀ n, (Pn n).IsFellerKernelSemigroup)

example {μ : Semigroup.PositiveShift} (f : C₀(alpha, ℝ)) (b : NNReal)
    (hres : ∀ g : C₀(alpha, ℝ), Filter.Tendsto
      (fun n ↦ (hFellern n).c0Semigroup.resolvent μ g) Filter.atTop
      (nhds (hFeller.c0Semigroup.resolvent μ g))) :
    TendstoUniformlyOn (fun n (t : NNReal) ↦ (hFellern n).c0Semigroup t f)
      (fun t ↦ hFeller.c0Semigroup t f) Filter.atTop (Set.Iic b) :=
  Semigroup.StronglyContinuousContractionSemigroup.tendstoUniformlyOn_operator_of_tendsto_resolvent
    hres f b

example {μ : Semigroup.PositiveShift} (f : C₀(alpha, ℝ))
    (hop : ∀ t : NNReal, Filter.Tendsto (fun n ↦ (hFellern n).c0Semigroup t f) Filter.atTop
      (nhds (hFeller.c0Semigroup t f))) :
    Filter.Tendsto (fun n ↦ (hFellern n).c0Semigroup.resolvent μ f) Filter.atTop
      (nhds (hFeller.c0Semigroup.resolvent μ f)) :=
  Semigroup.StronglyContinuousContractionSemigroup.tendsto_resolvent_of_tendsto_operator hop μ
end Convergence
```

The finite-dimensional distributions follow. For conservative Feller semigroups, strong
convergence of the `C₀` semigroups makes the finite-set laws converge against every compactly
supported continuous test *uniformly in the starting point*, and, at each fixed starting point,
against every bounded continuous test: that is weak convergence of the finite-dimensional
distributions. The upgrade from compactly supported to bounded continuous tests is where
conservativity is used a second time --- no mass escapes, because the limit is a probability
measure --- and it cannot be uniform in the starting point.

| fact | theorem |
| --- | --- |
| uniform convergence of the finite-set laws, compactly supported tests | `tendstoUniformly_integral_compactlySupported_finiteSetKernel` |
| weak convergence of the finite-dimensional laws | `tendsto_integral_boundedContinuous_finiteSetKernel` |
| the same for the process, at a finite set of times | `tendsto_integral_finsetEvaluation_continuousProcess` |
| one-time laws of the process | `tendsto_integral_eval_continuousProcess` |
| vague convergence to a probability measure is weak convergence | `tendsto_integral_boundedContinuous_of_tendsto_compactlySupported` |

```lean
section FiniteDimensional
variable (Pn : ℕ → SubMarkovKernelSemigroup alpha)
  (hFellern : ∀ n, (Pn n).IsFellerKernelSemigroup) (hPn : ∀ n, (Pn n).IsConservative)
  (hKn : ∀ n, (Pn n).KolmogorovRegular (hPn n)) (hKreg : P.KolmogorovRegular hP)
  (hstrong : ∀ (t : NNReal) (g : C₀(alpha, ℝ)),
    Filter.Tendsto (fun n ↦ (hFellern n).c0Semigroup t g) Filter.atTop
      (nhds (hFeller.c0Semigroup t g)))

example (I : Finset NNReal) (F : (I → alpha) →ᵇ ℝ) (x : alpha) :
    Filter.Tendsto (fun n ↦ ∫ path, F path ∂finiteSetKernel (Pn n) I x) Filter.atTop
      (nhds (∫ path, F path ∂finiteSetKernel P I x)) :=
  tendsto_integral_boundedContinuous_finiteSetKernel hFellern hPn hFeller hP hstrong I F x

example (I : Finset NNReal) (F : (I → alpha) →ᵇ ℝ) (x : alpha) :
    Filter.Tendsto (fun n ↦ ∫ omega, F (ContinuousPath.finsetEvaluation I omega)
        ∂(IsConservative.continuousProcess (Pn n) (hPn n) x)) Filter.atTop
      (nhds (∫ omega, F (ContinuousPath.finsetEvaluation I omega)
        ∂(IsConservative.continuousProcess P hP x))) :=
  tendsto_integral_finsetEvaluation_continuousProcess hFellern hPn hKn hFeller hP hKreg
    hstrong I F x
end FiniteDimensional
```

Finally, on path space. A **common** intrinsic moment bound `HasKolmogorovMoments p q M` for the
whole family makes the path laws at a fixed starting point tight, because the scale in the modulus
estimate of section 13 depends only on the exponents, the constant and the tolerances, never on
the semigroup. Cylinder approximation on the resulting compact set of paths then reduces weak
convergence to the finite-dimensional case. No compactness theorem for measures is used.

| fact | theorem |
| --- | --- |
| tightness of the family of path laws at a starting point | `isTightMeasureSet_insert_continuousProcess`, `exists_isCompact_measure_compl_le_insert` |
| convergence of every bounded continuous functional of the path | `tendsto_integral_continuousProcess` |
| the same, in the space of probability measures on path space | `tendsto_pathLaw` |
| the same, starting from the resolvents | `tendsto_pathLaw_of_tendsto_resolvent` |

```lean
section PathSpace
variable [ProperSpace alpha] (Pn : ℕ → SubMarkovKernelSemigroup alpha)
  (hFellern : ∀ n, (Pn n).IsFellerKernelSemigroup) (hPn : ∀ n, (Pn n).IsConservative)
  (hmomn : ∀ n, (Pn n).HasKolmogorovMoments p q M)
  (hstrong : ∀ (t : NNReal) (g : C₀(alpha, ℝ)),
    Filter.Tendsto (fun n ↦ (hFellern n).c0Semigroup t g) Filter.atTop
      (nhds (hFeller.c0Semigroup t g)))

example (F : ContinuousPath alpha →ᵇ ℝ) (x : alpha) :
    Filter.Tendsto
      (fun n ↦ ∫ omega, F omega ∂(IsConservative.continuousProcess (Pn n) (hPn n) x))
      Filter.atTop
      (nhds (∫ omega, F omega ∂(IsConservative.continuousProcess P hP x))) :=
  tendsto_integral_continuousProcess hFellern hPn hFeller hP hmomn hmom hstrong F x

example (x : alpha) :
    Filter.Tendsto (fun n ↦ IsConservative.pathLaw (Pn n) (hPn n) x) Filter.atTop
      (nhds (IsConservative.pathLaw P hP x)) :=
  tendsto_pathLaw hFellern hPn hFeller hP hmomn hmom hstrong x
end PathSpace
```

## 15. What the library does not contain

- Feller processes with càdlàg paths without a continuity criterion: the existence theorem asks
  for the Kolmogorov moment criterion and produces continuous paths.
- Weak continuity of the path law over a state space that is not proper: the tightness step of
  section 13 assumes that closed balls are compact.
- Prokhorov's theorem: tightness of a family of laws is proved, but not the relative compactness
  of that family in the topology of convergence in distribution.
- The multidimensional heat semigroup: `Examples/HeatSemigroup.lean` and
  `Examples/BrownianMotion.lean` build and identify Brownian motion on the line only, a
  multivariate Gaussian law not being available at the pinned Mathlib revision; no Lévy
  characterization, quadratic variation, or stochastic integral is proved.
- Augmented or right-continuous filtrations: every statement is for the raw canonical
  filtration.
- The generator form of the Trotter–Kato theorem (convergence of generators on a core) and the
  Trotter–Kurtz theorem for semigroups on a sequence of different spaces: section 14 states
  convergence on one Banach space through resolvents.
- Convergence of processes with different Kolmogorov moment constants, or on the Skorokhod space
  of càdlàg paths: section 14 asks for one common moment bound and works on `C([0, ∞), α)`.
