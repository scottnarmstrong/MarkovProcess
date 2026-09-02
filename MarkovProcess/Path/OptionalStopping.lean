/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Path.StoppingTimeDyadicCeiling
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Martingale.Basic

/-!
# Optional stopping in continuous time, at a bounded finite stopping time

Mathlib's optional stopping theorem is discrete-time.  This file proves the continuous-time
statement the library consumes: if `M` is a real-valued martingale for a filtration indexed by
`ℝ≥0`, bounded on bounded time intervals and right continuous in time along every sample point,
and `T` is a finite stopping time bounded by a deterministic horizon `K`, then

  `∫ omega, M (T omega) omega ∂mu = ∫ omega, M 0 omega ∂mu`

(`integral_stoppedValue_eq_of_locallyBounded`, with the uniformly bounded case
`integral_stoppedValue_eq_of_le`).

The route is elementary, and avoids reindexing through the `ℕ`-indexed theorem of Mathlib.  For a
stopping time `S` with finite range the identity `∫ M (S omega) omega = ∫ M u` for a horizon `u`
above the range is a finite sum over the values `v` of `S`: the event `{S = v}` lies in the
sigma-algebra at time `v`, so `∫_{S = v} M u = ∫_{S = v} M v` by the defining property of the
conditional expectation (`integral_apply_eq_of_finite_range`).  The dyadic ceilings `T_n` of a
finite stopping time are stopping times with finite range that decrease to `T`
(`Path/StoppingTimeDyadicCeiling.lean`), so the general case follows by dominated convergence,
using right continuity for the pointwise limit.

Nothing here is specific to path space: the statements are for an arbitrary measurable space with
a filtration indexed by `ℝ≥0`.
-/

open Filter MeasureTheory Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section

variable {Omega : Type*} {m : MeasurableSpace Omega} {mu : Measure Omega}
  {ℱ : Filtration NNReal m} {M : NNReal → Omega → ℝ}

section FiniteRange

variable [IsFiniteMeasure mu]

/-- A function of a time-valued map with values in a finite set is the sum of the indicators of
the level sets. -/
private theorem apply_eq_sum_indicator {S : Omega → NNReal} {V : Finset NNReal}
    (hSV : ∀ omega, S omega ∈ V) (g : NNReal → Omega → ℝ) (omega : Omega) :
    g (S omega) omega = ∑ v ∈ V, Set.indicator {eta | S eta = v} (g v) omega := by
  rw [Finset.sum_eq_single_of_mem (S omega) (hSV omega)]
  · rw [Set.indicator_of_mem (Set.mem_setOf_eq ▸ rfl)]
  · intro v _ hv
    exact Set.indicator_of_notMem (fun h ↦ hv h.symm) _

/-- The level sets of a stopping time with finite range are events of the filtration at the
corresponding time. -/
theorem measurableSet_eq_of_finite_range {S : Omega → NNReal}
    (hS : IsStoppingTime ℱ fun omega ↦ ((S omega : NNReal) : WithTop NNReal))
    (hfin : (Set.range S).Finite) (v : NNReal) :
    MeasurableSet[ℱ v] {omega | S omega = v} := by
  have hcount : (Set.range fun omega ↦ ((S omega : NNReal) : WithTop NNReal)).Countable := by
    refine (hfin.countable.image (fun w : NNReal ↦ (w : WithTop NNReal))).mono ?_
    rintro _ ⟨omega, rfl⟩
    exact ⟨S omega, ⟨omega, rfl⟩, rfl⟩
  have hset : {omega | S omega = v} =
      {omega | ((S omega : NNReal) : WithTop NNReal) = (v : WithTop NNReal)} := by
    ext omega
    simp only [Set.mem_setOf_eq, WithTop.coe_eq_coe]
  rw [hset]
  exact hS.measurableSet_eq_of_countable_range hcount v

/-- The value of an adapted process at a stopping time with finite range is measurable. -/
theorem stronglyMeasurable_apply_of_finite_range (hadapted : Adapted ℱ M) {S : Omega → NNReal}
    (hS : IsStoppingTime ℱ fun omega ↦ ((S omega : NNReal) : WithTop NNReal))
    (hfin : (Set.range S).Finite) :
    StronglyMeasurable fun omega ↦ M (S omega) omega := by
  have hSV : ∀ omega, S omega ∈ hfin.toFinset := fun omega ↦
    hfin.mem_toFinset.mpr ⟨omega, rfl⟩
  have hsum : (fun omega ↦ M (S omega) omega) =
      fun omega ↦ ∑ v ∈ hfin.toFinset, Set.indicator {eta | S eta = v} (M v) omega := by
    funext omega
    exact apply_eq_sum_indicator hSV M omega
  rw [hsum]
  refine Finset.stronglyMeasurable_fun_sum _ fun v _ ↦ ?_
  exact ((hadapted v).mono (ℱ.le v)).indicator
    (ℱ.le v _ (measurableSet_eq_of_finite_range hS hfin v))

/-- **Optional stopping at a stopping time with finite range.**  For a martingale `M` with
integrable values and a stopping time `S` with finite range bounded by the deterministic time
`u`, the expectation of `M` at time `S` is the expectation of `M` at time `u`.  This is a finite
sum over the values of `S`, each term handled by the defining property of the conditional
expectation on the event `{S = v}`, which belongs to the filtration at time `v`. -/
theorem integral_apply_eq_of_finite_range (hM : Martingale M ℱ mu)
    (hMint : ∀ t : NNReal, Integrable (M t) mu) {S : Omega → NNReal}
    (hS : IsStoppingTime ℱ fun omega ↦ ((S omega : NNReal) : WithTop NNReal))
    (hfin : (Set.range S).Finite) {u : NNReal} (hu : ∀ omega, S omega ≤ u) :
    ∫ omega, M (S omega) omega ∂mu = ∫ omega, M u omega ∂mu := by
  have hSV : ∀ omega, S omega ∈ hfin.toFinset := fun omega ↦
    hfin.mem_toFinset.mpr ⟨omega, rfl⟩
  have hmeas : ∀ v : NNReal, MeasurableSet[ℱ v] {omega | S omega = v} :=
    measurableSet_eq_of_finite_range hS hfin
  have hmeas' : ∀ v : NNReal, MeasurableSet {omega | S omega = v} := fun v ↦
    ℱ.le v _ (hmeas v)
  have hind : ∀ (g : NNReal → Omega → ℝ), (∀ t : NNReal, Integrable (g t) mu) →
      ∫ omega, g (S omega) omega ∂mu =
        ∑ v ∈ hfin.toFinset, ∫ omega in {omega | S omega = v}, g v omega ∂mu := by
    intro g hg
    have hsum : ∫ omega, g (S omega) omega ∂mu =
        ∫ omega, ∑ v ∈ hfin.toFinset, Set.indicator {eta | S eta = v} (g v) omega ∂mu :=
      integral_congr_ae (Eventually.of_forall fun omega ↦ apply_eq_sum_indicator hSV g omega)
    rw [hsum, integral_finset_sum _ fun v _ ↦ (hg v).indicator (hmeas' v)]
    exact Finset.sum_congr rfl fun v _ ↦ integral_indicator (hmeas' v)
  rw [hind M hMint, hind (fun _ ↦ M u) fun _ ↦ hMint u]
  refine Finset.sum_congr rfl fun v hv ↦ ?_
  have hle : v ≤ u := by
    obtain ⟨omega, rfl⟩ := hfin.mem_toFinset.mp hv
    exact hu omega
  rw [← setIntegral_condExp (ℱ.le v) (hMint u) (hmeas v)]
  exact (setIntegral_congr_ae (hmeas' v) ((hM.2 v u hle).mono fun _ hx _ ↦ hx)).symm

end FiniteRange

section DyadicApproximation

/-- One dyadic grid step is at most one. -/
private theorem inv_two_pow_le_one (n : ℕ) : ((2 : NNReal) ^ n)⁻¹ ≤ 1 := by
  rw [← NNReal.coe_le_coe, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_one]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- The dyadic ceiling of a time bounded by `K` is bounded by `K + 1`. -/
private theorem dyadicCeiling_le_add_one (n : ℕ) {t K : NNReal} (ht : t ≤ K) :
    dyadicCeiling n t ≤ K + 1 :=
  (dyadicCeiling_le_add n t).trans (add_le_add ht (inv_two_pow_le_one n))

/-- At each dyadic level, the ceilings of times bounded by a fixed horizon form a finite set. -/
private theorem finite_range_dyadicCeiling (n : ℕ) {S : Omega → NNReal} {K : NNReal}
    (hSK : ∀ omega, S omega ≤ K) :
    (Set.range fun omega ↦ dyadicCeiling n (S omega)).Finite := by
  refine Set.Finite.subset ((Set.finite_Iic (⌈(2 ^ n : ℝ) * (K : ℝ)⌉₊)).image
    (fun k : ℕ ↦ (⟨(k : ℝ) / 2 ^ n, by positivity⟩ : NNReal))) ?_
  rintro _ ⟨omega, rfl⟩
  refine ⟨⌈(2 ^ n : ℝ) * (S omega : ℝ)⌉₊, Set.mem_Iic.mpr (Nat.ceil_le_ceil ?_), rfl⟩
  exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (hSK omega))
    (by positivity : (0 : ℝ) ≤ 2 ^ n)

end DyadicApproximation

section OptionalStopping

variable [IsFiniteMeasure mu]

/-- **Optional stopping at a bounded finite stopping time**, for a martingale that is bounded on
bounded time intervals and right continuous in time.

Hypotheses: `M` is a martingale for the filtration `ℱ` under the finite measure `mu`; `hbound`
says that on every bounded time interval `[0, v]` the process is bounded by a constant depending
only on `v`; `hright` says that at every time `v` the orbit `t ↦ M t omega` is right continuous;
`T` is a stopping time bounded by the deterministic horizon `K`.  The conclusion is that the
expectation of `M` at time `T` is its expectation at time `0`.

The value of the process at the stopping time is Mathlib's `stoppedValue M T`, written out. -/
theorem integral_stoppedValue_eq_of_locallyBounded (hM : Martingale M ℱ mu)
    (hbound : ∀ v : NNReal, ∃ C : ℝ, ∀ t ≤ v, ∀ omega, ‖M t omega‖ ≤ C)
    (hright : ∀ (omega : Omega) (v : NNReal),
      ContinuousWithinAt (fun t : NNReal ↦ M t omega) (Set.Ici v) v)
    {T : Omega → NNReal}
    (hT : IsStoppingTime ℱ fun omega ↦ ((T omega : NNReal) : WithTop NNReal))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) :
    ∫ omega, M (T omega) omega ∂mu = ∫ omega, M 0 omega ∂mu := by
  have hMint : ∀ t : NNReal, Integrable (M t) mu := by
    intro t
    obtain ⟨C, hC⟩ := hbound t
    exact Integrable.of_bound ((hM.1 t).mono (ℱ.le t)).aestronglyMeasurable C
      (Eventually.of_forall (hC t le_rfl))
  have hzero : ∀ u : NNReal, ∫ omega, M u omega ∂mu = ∫ omega, M 0 omega ∂mu := by
    intro u
    rw [← integral_condExp (ℱ.le 0) (f := M u) (μ := mu)]
    exact integral_congr_ae (hM.2 0 u (zero_le u))
  have hstopfin : ∀ n : ℕ, (Set.range fun omega ↦ dyadicCeiling n (T omega)).Finite := fun n ↦
    finite_range_dyadicCeiling n hTK
  have hstep : ∀ n : ℕ,
      ∫ omega, M (dyadicCeiling n (T omega)) omega ∂mu = ∫ omega, M 0 omega ∂mu := by
    intro n
    rw [integral_apply_eq_of_finite_range hM hMint (isStoppingTime_dyadicCeiling hT n)
      (hstopfin n) (u := K + 1) fun omega ↦ dyadicCeiling_le_add_one n (hTK omega)]
    exact hzero _
  obtain ⟨C, hC⟩ := hbound (K + 1)
  have hptw : ∀ᵐ omega ∂mu, Tendsto (fun n ↦ M (dyadicCeiling n (T omega)) omega) atTop
      (𝓝 (M (T omega) omega)) := by
    refine Eventually.of_forall fun omega ↦ ?_
    have hnbhd : Tendsto (fun n ↦ dyadicCeiling n (T omega)) atTop (𝓝[≥] (T omega)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (tendsto_dyadicCeiling (T omega))
        (Eventually.of_forall fun n ↦ Set.mem_Ici.mpr (le_dyadicCeiling n (T omega)))
    exact Tendsto.comp (hright omega (T omega)) hnbhd
  have hlim := tendsto_integral_of_dominated_convergence (μ := mu) (fun _ ↦ C)
    (F := fun n omega ↦ M (dyadicCeiling n (T omega)) omega)
    (f := fun omega ↦ M (T omega) omega)
    (fun n ↦ (stronglyMeasurable_apply_of_finite_range hM.1
      (isStoppingTime_dyadicCeiling hT n) (hstopfin n)).aestronglyMeasurable)
    (integrable_const C)
    (fun n ↦ Eventually.of_forall fun omega ↦
      hC _ (dyadicCeiling_le_add_one n (hTK omega)) omega)
    hptw
  have hconst : Tendsto (fun n : ℕ ↦ ∫ omega, M (dyadicCeiling n (T omega)) omega ∂mu) atTop
      (𝓝 (∫ omega, M 0 omega ∂mu)) := by
    simp only [hstep]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hconst

/-- **Optional stopping at a bounded finite stopping time**, for a uniformly bounded martingale
with right continuous orbits: the expectation of `M` at a stopping time bounded by a
deterministic horizon is its expectation at time `0`. -/
theorem integral_stoppedValue_eq_of_le (hM : Martingale M ℱ mu) {C : ℝ}
    (hC : ∀ (t : NNReal) (omega : Omega), ‖M t omega‖ ≤ C)
    (hright : ∀ (omega : Omega) (v : NNReal),
      ContinuousWithinAt (fun t : NNReal ↦ M t omega) (Set.Ici v) v)
    {T : Omega → NNReal}
    (hT : IsStoppingTime ℱ fun omega ↦ ((T omega : NNReal) : WithTop NNReal))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) :
    ∫ omega, M (T omega) omega ∂mu = ∫ omega, M 0 omega ∂mu :=
  integral_stoppedValue_eq_of_locallyBounded hM (fun _ ↦ ⟨C, fun t _ omega ↦ hC t omega⟩) hright
    hT hTK

end OptionalStopping

end

end MarkovProcess
