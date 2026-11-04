/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import MarkovProcess.Trajectory.Dynkin
public import MarkovProcess.Feller.Resolvent
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
`d`-dimensional instance itself.

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

## Main statements

* `MarkovProcess.charFun_heatMeasure`: the characteristic function of `heatMeasure x t`.
* `MarkovProcess.heatMeasure_conv_heatMeasure`: the Gaussians convolve correctly.
* `MarkovProcess.heatMeasure_bind`: the Chapman--Kolmogorov law.
* `MarkovProcess.isConservative_heatSemigroupE`: every transition measure has mass one.
-/

public section

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

end

end MarkovProcess
