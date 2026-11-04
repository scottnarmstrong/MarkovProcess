/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import MarkovProcess.Trajectory.Dynkin
public import MarkovProcess.Feller.Resolvent
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The heat semigroup on a finite-dimensional inner product space

`MarkovProcess.Examples.HeatSemigroup` builds the heat semigroup on the real line, whose
transition measure at time `t` from `x` is the Gaussian law of mean `x` and variance `t`.  This
file does the same in finite dimensions: on a finite-dimensional real inner product space `E`,
the transition measure at time `t` from `x` is the Gaussian law of mean `x` and covariance
`t • id`, obtained by pushing Mathlib's `ProbabilityTheory.stdGaussian E` forward along
`z ↦ x + √t • z`.

Nothing in the existence machinery of this library is one-dimensional — `Examples.Drift` already
works on an arbitrary finite-dimensional real normed space — so the new content here is the
`d`-dimensional instance itself: the Chapman--Kolmogorov law, the Feller property, the Kolmogorov
moment bound, and hence the continuous-path process `brownianMotionE`.

The Chapman--Kolmogorov law is the one step whose one-dimensional proof does not transfer.
There it is `gaussianReal_conv_gaussianReal`, a lemma about real Gaussians; in finite dimensions
there is no such lemma, so `heatMeasure_conv_heatMeasure` goes through characteristic functions:
the characteristic function of `heatMeasure x t` is `exp (⟪x, ξ⟫ i) * exp (-t ‖ξ‖² / 2)`, these
multiply correctly in the mean and the covariance, and `MeasureTheory.Measure.ext_of_charFun`
turns that into equality of measures.

## Main definitions

* `MarkovProcess.heatMeasure x t`: the Gaussian law on `E` with mean `x` and covariance `t • id`.
* `MarkovProcess.heatKernelE t`: the same, as a kernel in the starting point.
* `MarkovProcess.heatSemigroupE`: the sub-Markov kernel semigroup they form.
* `MarkovProcess.brownianMotionE`: the continuous-path process it generates, a Brownian motion
  on `E`.

## Main statements

* `MarkovProcess.charFun_heatMeasure`: the characteristic function of `heatMeasure x t`.
* `MarkovProcess.heatMeasure_conv_heatMeasure`: the Gaussians convolve correctly.
* `MarkovProcess.heatMeasure_bind`: the Chapman--Kolmogorov law.
* `MarkovProcess.isConservative_heatSemigroupE`: every transition measure has mass one.
* `MarkovProcess.isFellerKernelSemigroupE`: the semigroup is Feller.
* `MarkovProcess.hasKolmogorovMoments_heatSemigroupE`: the Kolmogorov moment criterion holds with
  exponents `p = 4`, `q = 2` and the fourth moment of the standard Gaussian as constant.
* `MarkovProcess.existsUnique_continuousProcess_heatSemigroupE`: there is exactly one Markov
  kernel into continuous paths with these finite-dimensional distributions.
* `MarkovProcess.brownianMotionE_map_eval`: its one-time marginals are the Gaussian laws.

The one-dimensional file goes further and identifies the process as a Brownian motion in the
sense of independent Gaussian increments (`Examples.BrownianMotion`); the corresponding
identification in finite dimensions is not done here.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Complex
open scoped ENNReal NNReal ZeroAtInfty RealInnerProductSpace

namespace MarkovProcess

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section Definition

/-- The Gaussian law on `E` with mean `x` and covariance `t • id`: the image of the standard
Gaussian under `z ↦ x + √t • z`.  At `t = 0` this is the Dirac mass at `x`. -/
def heatMeasure (x : E) (t : ℝ≥0) : Measure E :=
  (stdGaussian E).map (fun z ↦ x + Real.sqrt t • z)

instance isProbabilityMeasure_heatMeasure (x : E) (t : ℝ≥0) :
    IsProbabilityMeasure (heatMeasure x t) := by
  rw [heatMeasure]
  infer_instance

omit [BorelSpace E] in
@[simp]
theorem heatMeasure_zero (x : E) : heatMeasure x 0 = Measure.dirac x := by
  have h : (fun z : E ↦ x + Real.sqrt (0 : ℝ≥0) • z) = fun _ ↦ x := by
    funext z; simp
  rw [heatMeasure, h, Measure.map_const]
  simp

/-- Translating the Gaussian law by a constant translates its mean. -/
theorem heatMeasure_eq_map_const_add (x : E) (t : ℝ≥0) :
    heatMeasure x t = (heatMeasure 0 t).map (fun u ↦ x + u) := by
  rw [heatMeasure, heatMeasure, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp

/-- Recentring the Gaussian law at its mean gives the centred Gaussian law. -/
theorem heatMeasure_map_sub_const (x : E) (t : ℝ≥0) :
    (heatMeasure x t).map (fun u ↦ u - x) = heatMeasure 0 t := by
  rw [heatMeasure_eq_map_const_add x t, Measure.map_map (by fun_prop) (by fun_prop)]
  have hid : (fun u : E ↦ u - x) ∘ (fun u : E ↦ x + u) = id := by
    funext u
    simp
  rw [hid, Measure.map_id]

end Definition

section CharFun

/-- The characteristic function of the Gaussian law with mean `x` and covariance `t • id`. -/
theorem charFun_heatMeasure (x : E) (t : ℝ≥0) (xi : E) :
    charFun (heatMeasure x t) xi = exp (⟪x, xi⟫ * I) * exp (-(t : ℝ) * ‖xi‖ ^ 2 / 2) := by
  have hmeas : Measurable (fun z : E ↦ x + Real.sqrt t • z) := by fun_prop
  rw [heatMeasure, charFun_apply, integral_map hmeas.aemeasurable
    (Measurable.aestronglyMeasurable (by fun_prop))]
  have hinner : ∀ z : E, (⟪x + Real.sqrt t • z, xi⟫ : ℝ) = ⟪x, xi⟫ + ⟪z, Real.sqrt t • xi⟫ := by
    intro z
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_right]
  simp_rw [hinner, ofReal_add, add_mul, exp_add]
  rw [integral_const_mul, ← charFun_apply, charFun_stdGaussian]
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    ← Complex.ofReal_pow, mul_pow, Real.sq_sqrt t.coe_nonneg]
  push_cast
  ring_nf

/-- **The Gaussians convolve correctly.**  Convolving the Gaussian of mean `x` and covariance
`s • id` with the Gaussian of mean `y` and covariance `t • id` gives the Gaussian of mean
`x + y` and covariance `(s + t) • id`.

This is the step that has no one-dimensional counterpart to borrow: `Examples.HeatSemigroup`
uses `gaussianReal_conv_gaussianReal`, and there is no such lemma in finite dimensions, so the
proof goes through characteristic functions. -/
theorem heatMeasure_conv_heatMeasure (x y : E) (s t : ℝ≥0) :
    (heatMeasure x s) ∗ (heatMeasure y t) = heatMeasure (x + y) (s + t) := by
  refine Measure.ext_of_charFun (funext fun xi ↦ ?_)
  rw [charFun_conv, charFun_heatMeasure, charFun_heatMeasure, charFun_heatMeasure,
    inner_add_left]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

end CharFun

section Kernel

/-- The Gaussian transition kernel of the heat semigroup, jointly in the time and the starting
point.  It is built from the standard Gaussian by the affine map `(t, x, z) ↦ x + √t • z`, which
makes joint measurability automatic. -/
def heatKernelJointE : Kernel (NNReal × E) E :=
  (Kernel.id ×ₖ Kernel.const (NNReal × E) (stdGaussian E)).map
    (fun q : (NNReal × E) × E ↦ q.1.2 + Real.sqrt q.1.1 • q.2)

theorem heatKernelJointE_apply (p : NNReal × E) : heatKernelJointE p = heatMeasure p.2 p.1 := by
  have hmeas : Measurable (fun q : (NNReal × E) × E ↦ q.1.2 + Real.sqrt q.1.1 • q.2) := by
    fun_prop
  have hpair : Measurable (fun z : E ↦ ((p : NNReal × E), z)) := by fun_prop
  rw [heatKernelJointE, Kernel.map_apply _ hmeas, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hmeas hpair]
  rfl

/-- The transition kernel of the heat semigroup at time `t`. -/
def heatKernelE (t : NNReal) : Kernel E E :=
  Kernel.comap heatKernelJointE (fun x : E ↦ (t, x)) (by fun_prop)

@[simp]
theorem heatKernelE_apply (t : NNReal) (x : E) : heatKernelE t x = heatMeasure x t := by
  rw [heatKernelE, Kernel.comap_apply, heatKernelJointE_apply]

instance isMarkovKernel_heatKernelE (t : NNReal) :
    IsMarkovKernel (heatKernelE (E := E) t) :=
  ⟨fun x ↦ by rw [heatKernelE_apply]; infer_instance⟩

/-- The mean of a Gaussian of fixed covariance is a measurable parameter. -/
theorem measurable_heatMeasure_left (t : NNReal) :
    Measurable (fun x : E ↦ heatMeasure x t) := by
  have hfun : (fun x : E ↦ heatMeasure x t) = fun x ↦ heatKernelE t x :=
    funext fun x ↦ (heatKernelE_apply t x).symm
  rw [hfun]
  exact (heatKernelE t).measurable

end Kernel

section Semigroup

/-- **The Chapman--Kolmogorov law.**  Sampling a Gaussian of covariance `s • id` and then, from
the value obtained, one of covariance `t • id`, gives a Gaussian of covariance `(s + t) • id`. -/
theorem heatMeasure_bind (x : E) (s t : ℝ≥0) :
    (heatMeasure x s).bind (fun y ↦ heatMeasure y t) = heatMeasure x (s + t) := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [Measure.lintegral_bind (measurable_heatMeasure_left t).aemeasurable hf.aemeasurable]
  have hinner : ∀ y : E, ∫⁻ z, f z ∂(heatMeasure y t)
      = ∫⁻ u, f (y + u) ∂(heatMeasure 0 t) := by
    intro y
    rw [heatMeasure_eq_map_const_add y t, lintegral_map hf (by fun_prop)]
  simp_rw [hinner]
  rw [← Measure.lintegral_conv hf, heatMeasure_conv_heatMeasure, add_zero]

/-- **The heat semigroup on a finite-dimensional inner product space.**  Its transition measure
at time `t` from `x` is the Gaussian law with mean `x` and covariance `t • id`. -/
def heatSemigroupE : SubMarkovKernelSemigroup E where
  kernel := heatKernelE
  measurable_kernel := by
    have hfun : (fun p : NNReal × E ↦ heatKernelE p.1 p.2) = fun p ↦ heatKernelJointE p := by
      funext p
      rw [heatKernelE, Kernel.comap_apply]
    rw [hfun]
    exact heatKernelJointE.measurable
  kernel_zero := Kernel.ext fun x ↦ by
    rw [heatKernelE_apply, heatMeasure_zero, Kernel.id_apply]
  kernel_add := fun s t ↦ Kernel.ext fun x ↦ by
    have hfun : ⇑(heatKernelE (E := E) t) = fun y ↦ heatMeasure y t :=
      funext (heatKernelE_apply t)
    rw [Kernel.comp_apply, heatKernelE_apply, heatKernelE_apply, hfun, heatMeasure_bind]
  isSubMarkovKernel := fun _ ↦ IsSubMarkovKernel.of_isMarkovKernel _

@[simp]
theorem heatSemigroupE_apply (t : ℝ≥0) (x : E) : heatSemigroupE t x = heatMeasure x t :=
  heatKernelE_apply t x

/-- The heat semigroup is conservative: every transition measure has total mass one. -/
theorem isConservative_heatSemigroupE : (heatSemigroupE (E := E)).IsConservative := by
  intro t x
  rw [heatSemigroupE_apply]
  exact measure_univ

end Semigroup

section Moments

/-- The fourth moment of the standard Gaussian on `E` is finite.  Every Gaussian measure on a
second-countable Banach space has moments of all orders, by Fernique's theorem. -/
theorem lintegral_enorm_pow_stdGaussian_lt_top :
    ∫⁻ z : E, ‖z‖ₑ ^ (4 : ℕ) ∂(stdGaussian E) < ⊤ := by
  have hmem : MemLp id ((4 : ℝ≥0) : ℝ≥0∞) (stdGaussian E) :=
    IsGaussian.memLp_id (stdGaussian E) _ (by simp)
  have hfin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := ((4 : ℝ≥0) : ℝ≥0∞)) (f := (id : E → E)) (by simp) (by simp) hmem.eLpNorm_lt_top
  have hp : (((4 : ℝ≥0) : ℝ≥0∞)).toReal = (4 : ℝ) := by simp
  rw [hp] at hfin
  simpa only [id_eq, ENNReal.rpow_ofNat] using hfin

variable (E) in
/-- The fourth moment of the standard Gaussian on `E`, as a nonnegative real number. -/
def stdGaussianFourthMoment : NNReal :=
  (∫⁻ z : E, ‖z‖ₑ ^ (4 : ℕ) ∂(stdGaussian E)).toNNReal

@[simp]
theorem coe_stdGaussianFourthMoment :
    (stdGaussianFourthMoment E : ℝ≥0∞) = ∫⁻ z : E, ‖z‖ₑ ^ (4 : ℕ) ∂(stdGaussian E) :=
  ENNReal.coe_toNNReal (ne_of_lt lintegral_enorm_pow_stdGaussian_lt_top)

private theorem enorm_sqrt_sq (h : ℝ≥0) :
    ‖Real.sqrt (h : ℝ)‖ₑ ^ (2 : ℕ) = (h : ℝ≥0∞) := by
  rw [← enorm_pow, Real.sq_sqrt h.coe_nonneg, Real.enorm_of_nonneg h.coe_nonneg,
    ENNReal.ofReal_coe_nnreal]

/-- **The heat semigroup satisfies the Kolmogorov moment criterion** with exponents `p = 4` and
`q = 2`, and the fourth moment of the standard Gaussian as constant: the fourth moment of the
displacement over a time step `h` is exactly `h ^ 2` times that constant. -/
theorem hasKolmogorovMoments_heatSemigroupE :
    (heatSemigroupE (E := E)).HasKolmogorovMoments 4 2 (stdGaussianFourthMoment E) := by
  refine ⟨by norm_num, by norm_num, fun h y ↦ ?_⟩
  have hmeasf : Measurable (fun w : E ↦ edist w y ^ (4 : ℝ)) :=
    (measurable_edist_left (x := y)).pow_const 4
  have hmeasg : Measurable (fun z : E ↦ y + Real.sqrt (h : ℝ) • z) := by fun_prop
  rw [heatSemigroupE_apply, heatMeasure, lintegral_map hmeasf hmeasg]
  have hint : ∀ z : E, edist (y + Real.sqrt (h : ℝ) • z) y ^ (4 : ℝ) =
      ‖Real.sqrt (h : ℝ)‖ₑ ^ (4 : ℕ) * ‖z‖ₑ ^ (4 : ℕ) := by
    intro z
    rw [ENNReal.rpow_ofNat, edist_eq_enorm_sub, add_sub_cancel_left, enorm_smul, mul_pow]
  simp_rw [hint]
  rw [lintegral_const_mul _ (by fun_prop), coe_stdGaussianFourthMoment, ENNReal.rpow_ofNat,
    show (4 : ℕ) = 2 * 2 from rfl, pow_mul, enorm_sqrt_sq]
  exact le_of_eq (mul_comm _ _)

end Moments

section Feller

/-- **The scaling representation of the heat semigroup.**  Integrating a `C₀` function against the
transition measure at time `t` from `x` is integrating its translate `z ↦ f (x + √t • z)` against
the standard Gaussian. -/
theorem kernelIntegral_heatSemigroupE (t : ℝ≥0) (f : C₀(E, ℝ)) (x : E) :
    kernelIntegral (heatSemigroupE t) f x =
      ∫ z, f (x + Real.sqrt t • z) ∂(stdGaussian E) := by
  rw [kernelIntegral, heatSemigroupE_apply, heatMeasure]
  exact integral_map (φ := fun z : E ↦ x + Real.sqrt t • z) (f := fun y : E ↦ f y)
    (by fun_prop) f.continuous.aestronglyMeasurable

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A `C₀` function is bounded by its norm. -/
theorem norm_apply_le_norm_c0E (f : C₀(E, ℝ)) (x : E) : ‖f x‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact f.toBCF.norm_coe_le_norm x

private theorem integrable_c0_compE (f : C₀(E, ℝ)) (t : ℝ≥0) (x : E) :
    Integrable (fun z ↦ f (x + Real.sqrt t • z)) (stdGaussian E) := by
  refine Integrable.mono' (integrable_const ‖f‖) ?_ (Filter.Eventually.of_forall fun z ↦ ?_)
  · exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact norm_apply_le_norm_c0E f _

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A finite measure on `E` puts arbitrarily little mass far from the origin. -/
theorem exists_measure_norm_ge_lt (nu : Measure E) [IsFiniteMeasure nu] {eps : ℝ}
    (heps : 0 < eps) : ∃ R : ℝ, 0 < R ∧ (nu {z : E | R ≤ ‖z‖}).toReal < eps := by
  have hmeasA : ∀ n : ℕ, NullMeasurableSet {z : E | (n : ℝ) ≤ ‖z‖} nu := fun n ↦
    ((isClosed_le continuous_const continuous_norm).measurableSet).nullMeasurableSet
  have hanti : Antitone (fun n : ℕ ↦ {z : E | (n : ℝ) ≤ ‖z‖}) := by
    intro n m hnm z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    exact le_trans (Nat.cast_le.mpr hnm) hz
  have hempty : (⋂ n : ℕ, {z : E | (n : ℝ) ≤ ‖z‖}) = (∅ : Set E) := by
    refine Set.eq_empty_of_forall_notMem fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
    exact absurd (Set.mem_iInter.mp hz n) (not_le.mpr hn)
  have htend := tendsto_measure_iInter_atTop hmeasA hanti ⟨0, measure_ne_top nu _⟩
  rw [hempty, measure_empty] at htend
  have hev : ∀ᶠ n : ℕ in atTop, nu {z : E | (n : ℝ) ≤ ‖z‖} < ENNReal.ofReal eps :=
    htend.eventually_lt_const (by simpa using heps)
  obtain ⟨n, hn⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
  exact ⟨(n : ℝ), by exact_mod_cast hn.2, ENNReal.toReal_lt_of_lt_ofReal hn.1⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- On a finite-dimensional normed space a property holds eventually along the cocompact filter
exactly when it holds at every point of large enough norm.  This replaces the one-dimensional
`cocompact_eq_atBot_atTop` argument. -/
theorem eventually_cocompact_iff_norm_ge {p : E → Prop} :
    (∀ᶠ x in cocompact E, p x) ↔ ∃ R : ℝ, ∀ x : E, R ≤ ‖x‖ → p x := by
  rw [← Metric.cobounded_eq_cocompact, Filter.hasBasis_cobounded_norm.eventually_iff]
  simp

/-- The heat semigroup maps `C₀` into itself. -/
theorem mapsC0_heatSemigroupE : (heatSemigroupE (E := E)).MapsC0 := by
  intro t f
  have hrep : kernelIntegral (heatSemigroupE t) f =
      fun x ↦ ∫ z, f (x + Real.sqrt t • z) ∂(stdGaussian E) :=
    funext (kernelIntegral_heatSemigroupE t f)
  rw [hrep]
  constructor
  · refine continuous_of_dominated (F := fun (x z : E) ↦ f (x + Real.sqrt t • z))
      (bound := fun _ ↦ ‖f‖) ?_ ?_ (integrable_const (μ := stdGaussian E) ‖f‖) ?_
    · exact fun x ↦ (f.continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact fun x ↦ Filter.Eventually.of_forall fun z ↦ norm_apply_le_norm_c0E f _
    · exact Filter.Eventually.of_forall fun z ↦ f.continuous.comp (by fun_prop)
  · rw [Metric.tendsto_nhds]
    intro eps heps
    rw [eventually_cocompact_iff_norm_ge]
    obtain ⟨R2, hR2pos, hR2⟩ := exists_measure_norm_ge_lt (E := E) (stdGaussian E)
      (eps := eps / (2 * (‖f‖ + 1))) (by positivity)
    have hfev : ∀ᶠ y : E in cocompact E, ‖f y‖ ≤ eps / 2 := by
      have := Metric.tendsto_nhds.mp f.zero_at_infty' (eps / 2) (by positivity)
      filter_upwards [this] with y hy
      simpa [dist_eq_norm] using hy.le
    obtain ⟨R1, hR1⟩ := eventually_cocompact_iff_norm_ge.mp hfev
    refine ⟨R1 + Real.sqrt t * R2, fun x hx ↦ ?_⟩
    set S : Set E := {z : E | R2 ≤ ‖z‖} with hS
    have hSmeas : MeasurableSet S :=
      (isClosed_le continuous_const continuous_norm).measurableSet
    set bound : E → ℝ := fun z ↦ eps / 2 + ‖f‖ * S.indicator (fun _ ↦ (1 : ℝ)) z with hbound
    have hindInt : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) (stdGaussian E) :=
      (integrable_indicator_iff hSmeas).mpr (integrableOn_const (measure_ne_top _ _))
    have hboundInt : Integrable bound (stdGaussian E) :=
      (integrable_const (μ := stdGaussian E) (eps / 2)).add (hindInt.const_mul _)
    have hptwise : ∀ z : E, ‖f (x + Real.sqrt t • z)‖ ≤ bound z := by
      intro z
      by_cases hz : z ∈ S
      · rw [hbound]
        simp only [Set.indicator_of_mem hz, mul_one]
        have := norm_apply_le_norm_c0E f (x + Real.sqrt t • z)
        linarith only [this, heps]
      · have hzlt : ‖z‖ < R2 := lt_of_not_ge (by simpa only [hS, Set.mem_ofPred_eq] using hz)
        have hge : R1 ≤ ‖x + Real.sqrt t • z‖ := by
          have h1 : ‖Real.sqrt t • z‖ ≤ Real.sqrt t * R2 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
            exact mul_le_mul_of_nonneg_left hzlt.le (Real.sqrt_nonneg _)
          have h2 : ‖x‖ - ‖Real.sqrt t • z‖ ≤ ‖x + Real.sqrt t • z‖ := by
            have := norm_sub_norm_le x (-(Real.sqrt t • z))
            simpa [sub_neg_eq_add] using this
          linarith only [hx, h1, h2]
        rw [hbound]
        simp only [Set.indicator_of_notMem hz, mul_zero, add_zero]
        exact hR1 _ hge
    have hintegral : ∫ z, bound z ∂(stdGaussian E) ≤ eps / 2 + ‖f‖ * (eps / (2 * (‖f‖ + 1))) := by
      rw [hbound, integral_add (integrable_const (μ := stdGaussian E) (eps / 2))
        (hindInt.const_mul _), integral_const, MeasureTheory.integral_const_mul,
        integral_indicator_const (1 : ℝ) hSmeas, probReal_univ]
      simp only [smul_eq_mul, mul_one]
      have : ((stdGaussian E).real S) ≤ eps / (2 * (‖f‖ + 1)) := hR2.le
      have hnn : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
      nlinarith only [this, hnn, measureReal_nonneg (μ := stdGaussian E) (s := S)]
    have hfinal : ‖∫ z, f (x + Real.sqrt t • z) ∂(stdGaussian E)‖ ≤ eps / 2 + ‖f‖ * (eps / (2 * (‖f‖ + 1))) :=
      le_trans (norm_integral_le_of_norm_le hboundInt
        (Filter.Eventually.of_forall hptwise)) hintegral
    have hstrict : ‖f‖ * (eps / (2 * (‖f‖ + 1))) < eps / 2 := by
      have hnn : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
      have key : ‖f‖ * (eps / (2 * (‖f‖ + 1))) = (‖f‖ / (‖f‖ + 1)) * (eps / 2) := by
        field_simp
      have hfrac : ‖f‖ / (‖f‖ + 1) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith only [hnn]
      rw [key]
      calc (‖f‖ / (‖f‖ + 1)) * (eps / 2) < 1 * (eps / 2) :=
            mul_lt_mul_of_pos_right hfrac (by positivity)
        _ = eps / 2 := one_mul _
    rw [dist_eq_norm, sub_zero]
    linarith only [hfinal, hstrict]

/-- The `C₀` orbit displacement of the heat semigroup is uniformly small over short times: for
every `ε > 0` there is a `δ > 0` such that the transition operator moves a `C₀` function by at
most `ε` in the uniform norm over every time shorter than `δ`. -/
theorem exists_norm_c0Operator_sub_le_heatSemigroupE (f : C₀(E, ℝ)) {eps : ℝ} (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ≥0, (h : ℝ) < delta →
      ‖(heatSemigroupE (E := E)).c0Operator mapsC0_heatSemigroupE h f - f‖ ≤ eps := by
  obtain ⟨delta0, hdelta0, huc⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous f) (eps / 2) (half_pos heps)
  obtain ⟨R, hR, hRmeas⟩ := exists_measure_norm_ge_lt (E := E) (stdGaussian E)
    (eps := eps / (4 * (‖f‖ + 1))) (by positivity)
  set S : Set E := {z : E | R ≤ ‖z‖} with hS
  have hSmeas : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  set bound : E → ℝ := fun z ↦ eps / 2 + 2 * ‖f‖ * S.indicator (fun _ ↦ (1 : ℝ)) z with hbound
  have hindInt : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) (stdGaussian E) :=
    (integrable_indicator_iff hSmeas).mpr (integrableOn_const (measure_ne_top _ _))
  have hboundInt : Integrable bound (stdGaussian E) :=
    (integrable_const (μ := stdGaussian E) (eps / 2)).add (hindInt.const_mul _)
  have hboundIntegral : ∫ z, bound z ∂(stdGaussian E) ≤ eps := by
    rw [hbound, integral_add (integrable_const (μ := stdGaussian E) (eps / 2))
      (hindInt.const_mul _), integral_const, MeasureTheory.integral_const_mul,
      integral_indicator_const (1 : ℝ) hSmeas]
    have hnorm : 0 ≤ ‖f‖ := norm_nonneg f
    have hkey : 2 * ‖f‖ * ((stdGaussian E).real S) ≤ eps / 2 := by
      have hpos : (0 : ℝ) ≤ (stdGaussian E).real S := measureReal_nonneg
      calc 2 * ‖f‖ * ((stdGaussian E).real S)
          ≤ 2 * (‖f‖ + 1) * (eps / (4 * (‖f‖ + 1))) := by
            apply mul_le_mul _ (le_of_lt hRmeas) hpos (by positivity)
            exact mul_le_mul_of_nonneg_left (by linarith only []) (by norm_num)
        _ = eps / 2 := by field_simp; ring
    rw [probReal_univ]
    simp only [smul_eq_mul, mul_one]
    linarith only [hkey]
  refine ⟨(delta0 / R) ^ 2, by positivity, fun h hh ↦ ?_⟩
  have hsqrt : Real.sqrt h * R < delta0 := by
    have h1 : Real.sqrt h < delta0 / R := by
      have := Real.sqrt_lt_sqrt h.coe_nonneg hh
      rwa [Real.sqrt_sq (by positivity)] at this
    calc Real.sqrt h * R < (delta0 / R) * R := mul_lt_mul_of_pos_right h1 hR
      _ = delta0 := div_mul_cancel₀ delta0 (ne_of_gt hR)
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (le_of_lt heps)).2 fun x ↦ ?_
  show ‖(heatSemigroupE (E := E)).c0Operator mapsC0_heatSemigroupE h f x - f x‖ ≤ eps
  rw [SubMarkovKernelSemigroup.c0Operator_apply, kernelIntegral_heatSemigroupE]
  have hsub : (∫ z, f (x + Real.sqrt h • z) ∂(stdGaussian E)) - f x =
      ∫ z, (f (x + Real.sqrt h • z) - f x) ∂(stdGaussian E) := by
    rw [integral_sub (integrable_c0_compE f h x) (integrable_const (f x)), integral_const,
      probReal_univ, one_smul]
  rw [hsub]
  refine le_trans (norm_integral_le_of_norm_le hboundInt
    (Filter.Eventually.of_forall fun z ↦ ?_)) hboundIntegral
  by_cases hz : z ∈ S
  · have h1 : ‖f (x + Real.sqrt h • z) - f x‖ ≤ 2 * ‖f‖ := by
      calc ‖f (x + Real.sqrt h • z) - f x‖ ≤ ‖f (x + Real.sqrt h • z)‖ + ‖f x‖ :=
            norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (norm_apply_le_norm_c0E f _) (norm_apply_le_norm_c0E f _)
        _ = 2 * ‖f‖ := by ring
    rw [hbound]
    simp only [Set.indicator_of_mem hz, mul_one]
    linarith only [h1, heps]
  · have hdist : dist (x + Real.sqrt h • z) x < delta0 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hzR : ‖z‖ < R := lt_of_not_ge (by simpa only [hS, Set.mem_ofPred_eq] using hz)
      calc Real.sqrt h * ‖z‖ ≤ Real.sqrt h * R :=
            mul_le_mul_of_nonneg_left (le_of_lt hzR) (Real.sqrt_nonneg _)
        _ < delta0 := hsqrt
    have h2 : ‖f (x + Real.sqrt h • z) - f x‖ ≤ eps / 2 := by
      rw [← dist_eq_norm]
      exact le_of_lt (huc hdist)
    rw [hbound]
    simp only [Set.indicator_of_notMem hz, mul_zero, add_zero]
    exact h2

/-- The `C₀` orbits of the heat semigroup are continuous in time. -/
theorem hasContinuousC0Orbits_heatSemigroupE :
    (heatSemigroupE (E := E)).HasContinuousC0Orbits mapsC0_heatSemigroupE := by
  intro f
  rw [Metric.continuous_iff]
  intro b eps heps
  obtain ⟨delta, hdelta, hkey⟩ :=
    exists_norm_c0Operator_sub_le_heatSemigroupE f (half_pos heps)
  refine ⟨delta, hdelta, fun a hab ↦ ?_⟩
  have hcontraction : ∀ c d : ℝ≥0, c ≤ d → (d : ℝ) - (c : ℝ) < delta →
      dist ((heatSemigroupE (E := E)).c0Operator mapsC0_heatSemigroupE d f)
        ((heatSemigroupE (E := E)).c0Operator mapsC0_heatSemigroupE c f) ≤ eps / 2 := by
    intro c d hcd hlt
    have hdc : c + (d - c) = d := add_tsub_cancel_of_le hcd
    have hcoe : ((d - c : ℝ≥0) : ℝ) < delta := by
      rw [NNReal.coe_sub hcd]
      exact hlt
    have hop : (heatSemigroupE (E := E)).c0Operator mapsC0_heatSemigroupE d f =
        (heatSemigroupE (E := E)).c0Operator mapsC0_heatSemigroupE c
          ((heatSemigroupE (E := E)).c0Operator mapsC0_heatSemigroupE (d - c) f) := by
      conv_lhs => rw [← hdc]
      rw [SubMarkovKernelSemigroup.c0Operator_add]
      rfl
    rw [dist_eq_norm, hop, ← map_sub]
    calc ‖(heatSemigroupE (E := E)).c0Operator mapsC0_heatSemigroupE c
            ((heatSemigroupE (E := E)).c0Operator mapsC0_heatSemigroupE (d - c) f - f)‖
        ≤ ‖(heatSemigroupE (E := E)).c0Operator mapsC0_heatSemigroupE c‖ *
            ‖(heatSemigroupE (E := E)).c0Operator mapsC0_heatSemigroupE (d - c) f - f‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (eps / 2) := by
          refine mul_le_mul (SubMarkovKernelSemigroup.norm_c0Operator_le _ _ c)
            (hkey _ hcoe) (norm_nonneg _) zero_le_one
      _ = eps / 2 := one_mul _
  have habs : |(a : ℝ) - (b : ℝ)| < delta := by
    rw [← NNReal.dist_eq]
    exact hab
  rcases le_total b a with hba | hab'
  · have := hcontraction b a hba (by
      rw [abs_of_nonneg (by
        have : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
        linarith only [this])] at habs
      exact habs)
    linarith only [this, heps]
  · have := hcontraction a b hab' (by
      rw [abs_sub_comm, abs_of_nonneg (by
        have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab'
        linarith only [this])] at habs
      exact habs)
    rw [dist_comm]
    linarith only [this, heps]

/-- **The heat semigroup on a finite-dimensional inner product space is Feller.** -/
theorem isFellerKernelSemigroupE : (heatSemigroupE (E := E)).IsFellerKernelSemigroup :=
  ⟨mapsC0_heatSemigroupE, hasContinuousC0Orbits_heatSemigroupE⟩

end Feller

section Process

/-- The heat semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_heatSemigroupE :
    (heatSemigroupE (E := E)).KolmogorovRegular isConservative_heatSemigroupE :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    isConservative_heatSemigroupE hasKolmogorovMoments_heatSemigroupE

/-- **The main theorem of the library, applied in finite dimensions.**  There is exactly one
Markov kernel from `E` to continuous paths in `E` whose finite-dimensional distributions are the
Gaussian transition laws of the heat semigroup. -/
theorem existsUnique_continuousProcess_heatSemigroupE :
    ∃! Q : Kernel E (ContinuousPath E), IsMarkovKernel Q ∧
      ∀ I : Finset ℝ≥0,
        Q.map (ContinuousPath.finsetEvaluation I) =
          SubMarkovKernelSemigroup.finiteSetKernel (heatSemigroupE (E := E)) I :=
  isFellerKernelSemigroupE.existsUnique_continuousProcess_of_hasKolmogorovMoments
    heatSemigroupE isConservative_heatSemigroupE hasKolmogorovMoments_heatSemigroupE

/-- **Brownian motion on a finite-dimensional inner product space**, as a Markov kernel from the
starting point to continuous paths: the continuous-path process of the heat semigroup. -/
def brownianMotionE : Kernel E (ContinuousPath E) :=
  SubMarkovKernelSemigroup.IsConservative.continuousProcess heatSemigroupE
    isConservative_heatSemigroupE

instance isMarkovKernel_brownianMotionE : IsMarkovKernel (brownianMotionE (E := E)) := by
  unfold brownianMotionE
  infer_instance

/-- Every one-time marginal of Brownian motion started at `x` is the Gaussian law with mean `x`
and covariance the elapsed time times the identity. -/
theorem brownianMotionE_map_eval (t : ℝ≥0) (x : E) :
    (brownianMotionE x).map (fun omega ↦ omega t) = heatMeasure x t := by
  have hmeas : Measurable (fun omega : ContinuousPath E ↦ omega t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := E) t
  rw [brownianMotionE, ← Kernel.map_apply _ hmeas,
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_eval_nnreal
      heatSemigroupE isConservative_heatSemigroupE isFellerKernelSemigroupE
      kolmogorovRegular_heatSemigroupE t, heatSemigroupE_apply]

/-- Every finite-dimensional distribution of Brownian motion is the corresponding finite-set
kernel of the heat semigroup. -/
theorem brownianMotionE_map_finsetEvaluation (I : Finset ℝ≥0) :
    (brownianMotionE (E := E)).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel (heatSemigroupE (E := E)) I :=
  isFellerKernelSemigroupE.continuousProcess_map_finiteEvaluation heatSemigroupE
    isConservative_heatSemigroupE kolmogorovRegular_heatSemigroupE I

/-- Brownian motion is the only Markov kernel into continuous paths with the finite-dimensional
distributions of the heat semigroup. -/
theorem eq_brownianMotionE_of_map_finsetEvaluation (Q : Kernel E (ContinuousPath E))
    [IsFiniteKernel Q]
    (hQ : ∀ I : Finset ℝ≥0,
      Q.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel (heatSemigroupE (E := E)) I) :
    Q = brownianMotionE :=
  SubMarkovKernelSemigroup.IsConservative.eq_continuousProcess_of_map_finiteEvaluation
    heatSemigroupE isConservative_heatSemigroupE kolmogorovRegular_heatSemigroupE Q hQ

end Process

end

end MarkovProcess
