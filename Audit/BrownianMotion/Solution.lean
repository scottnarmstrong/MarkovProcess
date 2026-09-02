import MarkovProcess.Examples.BrownianMotion
import MarkovProcess.Examples.HeatGenerator
import Audit.BrownianMotion.SolutionBasic

/-!
# Brownian motion — comparator solution

Proves the challenge theorem `BrownianMotionChallenge.brownianMotion` from the library.  The
challenge's vocabulary (`SolutionBasic.lean`, a verbatim Mathlib-only copy of the challenge) is
bridged to the library's definitions by the private lemmas below: the challenge's heat kernel is
the library's `heatSemigroup` at each time, the two recursively defined finite-time kernels agree
by structural induction, and the challenge's `IsBrownianReal` has the fields of the library's.
The three conjuncts are then `existsUnique_continuousProcess_heatSemigroup`,
`eq_brownianMotion_of_map_finsetEvaluation` with `isBrownianReal_brownianMotion`, and
`tendstoUniformly_gaussianAverage_sub_div`, transported along those bridges.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace BrownianMotionChallenge

section Bridges

/-- The challenge's heat kernel is the library's heat semigroup at that time. -/
private theorem heatKernel_eq (t : NNReal) : heatKernel t = MarkovProcess.heatSemigroup t :=
  Kernel.ext fun x ↦ (MarkovProcess.heatSemigroup_apply t x).symm

/-- The two recursively defined finite-time kernels agree. -/
private theorem heatFiniteTimeKernel_eq :
    ∀ {n : ℕ} (times : FiniteOrderedTimes n),
      heatFiniteTimeKernel times =
        MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel MarkovProcess.heatSemigroup times
  | 0, _ => rfl
  | n + 1, times => by
      show Kernel.mapOfMeasurable
          (heatKernel (times 0) ⊗ₖ Kernel.prodMkLeft ℝ
            (heatFiniteTimeKernel times.relativeTail)) _ _ = _
      rw [heatFiniteTimeKernel_eq times.relativeTail, heatKernel_eq]
      rfl

private theorem heatFiniteSetKernel_eq (I : Finset NNReal) :
    heatFiniteSetKernel I =
      MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel MarkovProcess.heatSemigroup I := by
  unfold heatFiniteSetKernel MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
  rw [heatFiniteTimeKernel_eq]
  rfl

private theorem finsetEvaluation_eq (I : Finset NNReal) :
    (ContinuousPath.finsetEvaluation (α := ℝ) I) =
      MarkovProcess.ContinuousPath.finsetEvaluation (alpha := ℝ) I := rfl

/-- The library's Brownian predicate has the fields of the challenge's. -/
private theorem isBrownianReal_of_lib {Ω : Type*} [MeasurableSpace Ω] {X : NNReal → Ω → ℝ}
    {P : Measure Ω} (h : MarkovProcess.IsBrownianReal X P) : IsBrownianReal X P :=
  ⟨h.hasLaw_eval, h.hasIndepIncrements, h.cont⟩

end Bridges

open ContinuousPath in
/-- **Brownian motion is the continuous Markov process of the heat semigroup, and its
generator is half the Laplacian.**  There is exactly one Markov kernel from `ℝ` to continuous
paths with the finite-dimensional distributions of the heat kernels; under it, from every
starting point `x`, the centred canonical process is a Brownian motion; and for every twice
continuously differentiable `f` with `f` and `f''` vanishing at infinity, the difference
quotients `t⁻¹ (P_t f − f)` converge to `½ f''` uniformly as `t → 0⁺`. -/
theorem brownianMotion :
    (∃! Q : Kernel ℝ (ContinuousPath ℝ), IsMarkovKernel Q ∧
        ∀ I : Finset NNReal, Q.map (ContinuousPath.finsetEvaluation I) = heatFiniteSetKernel I) ∧
    (∀ Q : Kernel ℝ (ContinuousPath ℝ), IsMarkovKernel Q →
        (∀ I : Finset NNReal, Q.map (ContinuousPath.finsetEvaluation I) = heatFiniteSetKernel I) →
        ∀ x : ℝ, IsBrownianReal (fun (t : NNReal) (ω : ContinuousPath ℝ) ↦ ω t - x) (Q x)) ∧
    (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → Tendsto f (cocompact ℝ) (𝓝 0) →
        Tendsto (iteratedDeriv 2 f) (cocompact ℝ) (𝓝 0) →
        TendstoUniformly
          (fun (t : NNReal) (x : ℝ) ↦ (t : ℝ)⁻¹ * ((∫ y, f y ∂gaussianReal x t) - f x))
          (fun x ↦ iteratedDeriv 2 f x / 2) (𝓝[>] 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := MarkovProcess.existsUnique_continuousProcess_heatSemigroup
    simpa only [heatFiniteSetKernel_eq, finsetEvaluation_eq] using h
  · intro Q hQ hI x
    haveI := hQ
    have hQ' : Q = MarkovProcess.brownianMotion := by
      refine MarkovProcess.eq_brownianMotion_of_map_finsetEvaluation Q fun I ↦ ?_
      rw [← heatFiniteSetKernel_eq, ← finsetEvaluation_eq]
      exact hI I
    rw [hQ']
    exact isBrownianReal_of_lib (MarkovProcess.isBrownianReal_brownianMotion x)
  · intro f hf h0 h2
    exact MarkovProcess.tendstoUniformly_gaussianAverage_sub_div hf h0 h2

end BrownianMotionChallenge
