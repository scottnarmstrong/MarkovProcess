/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import MarkovProcess.Examples.BrownianMotion
public import MarkovProcess.Examples.HeatSemigroupEuclidean

/-!
# The process of the finite-dimensional heat semigroup is a Brownian motion

`MarkovProcess.Examples.BrownianMotion` identifies the continuous-path process of the
one-dimensional heat semigroup as a Brownian motion on the line.  This file does the same for the
process `brownianMotionE` of `Examples.HeatSemigroupEuclidean` on a finite-dimensional real inner
product space `E`: recentred at its starting point it has centred Gaussian marginals of
covariance the elapsed time times the identity, independent increments over the consecutive
intervals of every finite monotone family of times, and continuous trajectories.

The engine is the same as in one dimension: the simple Markov property in joint-law form
(`brownianMotionE_map_prodMk_shift`), iterated to identify the law of the vector of increments of
a monotone family of times as a product of centred Gaussians, with independence following from
the product form.

Reused from the one-dimensional file, because they do not mention the state space:
`timeIncrements` and its lemmas, and the definition `HasIndepIncrements`.  The increment map
itself is restated for `E`, since the one-dimensional `incrementsMap` is typed in `ℝ`.

Main results:

* `brownianMotionE_map_prodMk_shift`: the simple Markov property in joint-law form.
* `brownianMotionE_map_incrementsMap`, `brownianMotionE_map_increments`: the joint law of the
  increments is a product of centred Gaussians.
* `hasIndepIncrements_brownianMotionE`: independence of the increments.
* `IsBrownianE`, `isBrownianE_brownianMotionE`: the identification.

As in one dimension, no Lévy characterization, quadratic variation, or stochastic integral is
asserted.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

section MarkovProperty

/-- A joint law factorizes through a kernel as soon as the law of the second variable, after
restriction to every event determined by the first, is the kernel composed with that restriction.

This is the state-space-free computation of `Examples.BrownianMotion`, repeated here because it
is `private` there. -/
private theorem map_prodMk_eq_compProd_of_restrict_map'
    {Omega beta gamma : Type*} {mOmega : MeasurableSpace Omega}
    {mBeta : MeasurableSpace beta} {mGamma : MeasurableSpace gamma}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → beta) (hX : Measurable X)
    (Y : Omega → gamma) (hY : Measurable Y)
    (kappa : Kernel beta gamma) [IsMarkovKernel kappa]
    (hrestrict : ∀ C : Set beta, MeasurableSet C →
      (mu.restrict (X ⁻¹' C)).map Y = kappa.comap X hX ∘ₘ (mu.restrict (X ⁻¹' C))) :
    mu.map (fun omega ↦ (X omega, Y omega)) = (mu.map X) ⊗ₘ kappa := by
  refine MeasureTheory.ext_of_generate_finite _ generateFrom_prod.symm
    isPiSystem_prod ?_ ?_
  · rintro _ ⟨C, hC, B, hB, rfl⟩
    have hleft : mu.map (fun omega ↦ (X omega, Y omega)) (C ×ˢ B)
        = ∫⁻ omega in X ⁻¹' C, kappa (X omega) B ∂mu := by
      rw [Measure.map_apply (hX.prodMk hY) (hC.prod hB), Set.mk_preimage_prod,
        Set.inter_comm, ← Measure.restrict_apply (hY hB), ← Measure.map_apply hY hB,
        hrestrict C hC, Measure.bind_apply hB (Kernel.aemeasurable _)]
      simp_rw [Kernel.comap_apply]
    rw [hleft, Measure.compProd_apply_prod hC hB, setLIntegral_map hC (kappa.measurable_coe hB) hX]
  · rw [measure_univ, measure_univ]

/-- **The simple Markov property of Brownian motion on `E`, in joint-law form.** -/
theorem brownianMotionE_map_prodMk_shift (x : E) (s : ℝ≥0) :
    (brownianMotionE x).map (fun omega ↦ (omega s, ContinuousPath.shift s omega)) =
      (heatMeasure x s) ⊗ₘ brownianMotionE := by
  have hX : Measurable (fun omega : ContinuousPath E ↦ omega s) :=
    ContinuousPath.measurable_coordinateProcess s
  have hY : Measurable (ContinuousPath.shift (alpha := E) s) :=
    ContinuousPath.measurable_shift_fixed s
  rw [← brownianMotionE_map_eval s x]
  refine map_prodMk_eq_compProd_of_restrict_map' (brownianMotionE x) _ hX _ hY brownianMotionE ?_
  intro C hC
  have hA : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := E) s]
      ((fun omega : ContinuousPath E ↦ omega s) ⁻¹' C) :=
    ContinuousPath.measurable_coordinateProcess_canonicalFiltration s hC
  exact SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift
    heatSemigroupE isConservative_heatSemigroupE isFellerKernelSemigroupE
    kolmogorovRegular_heatSemigroupE x s _ hA

end MarkovProperty

section Increments

/-- The increments of a finite coordinate path in `E`, the first one measured from a base point. -/
def incrementsMapE : {n : ℕ} → E → (Fin n → E) → (Fin n → E)
  | 0, _, _ => fun i ↦ i.elim0
  | _ + 1, x, path => Fin.cons (path 0 - x) (incrementsMapE (path 0) (Fin.tail path))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The recursion defining the increments. -/
theorem incrementsMapE_succ {n : ℕ} (x : E) (path : Fin (n + 1) → E) :
    incrementsMapE x path = Fin.cons (path 0 - x) (incrementsMapE (path 0) (Fin.tail path)) :=
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The first increment is the displacement from the base point. -/
@[simp]
theorem incrementsMapE_zero_apply {n : ℕ} (x : E) (path : Fin (n + 1) → E) :
    incrementsMapE x path 0 = path 0 - x := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Every increment after the first is the difference of two consecutive coordinates. -/
theorem incrementsMapE_succ_apply : ∀ {n : ℕ} (x : E) (path : Fin (n + 1) → E) (i : Fin n),
    incrementsMapE x path i.succ = path i.succ - path i.castSucc := by
  intro n
  induction n with
  | zero => exact fun _ _ i ↦ i.elim0
  | succ n ih =>
    intro x path i
    rw [incrementsMapE_succ, Fin.cons_succ]
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [incrementsMapE_zero_apply]
      rfl
    · rw [ih (path 0) (Fin.tail path) j, Fin.tail, Fin.tail, ← Fin.succ_castSucc]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The increments of a finite coordinate path, in closed form. -/
theorem incrementsMapE_eq_cons {n : ℕ} (x : E) (path : Fin (n + 1) → E) :
    incrementsMapE x path =
      Fin.cons (path 0 - x) (fun i : Fin n ↦ path i.succ - path i.castSucc) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [incrementsMapE_zero_apply, Fin.cons_zero]
  · rw [incrementsMapE_succ_apply, Fin.cons_succ]

/-- Taking increments is measurable, jointly in the base point and the path. -/
theorem measurable_incrementsMapE {n : ℕ} :
    Measurable (fun p : E × (Fin n → E) ↦ incrementsMapE p.1 p.2) := by
  cases n with
  | zero => exact Measurable.of_eval fun i ↦ i.elim0
  | succ n =>
    simp_rw [incrementsMapE_eq_cons]
    refine measurable_pi_iff.mpr fun i ↦ ?_
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.cons_zero]
      fun_prop
    · simp only [Fin.cons_succ]
      fun_prop

/-- Reading a path at a finite family of times and taking increments is measurable. -/
theorem measurable_incrementsMapE_eval {n : ℕ} (s : Fin n → ℝ≥0) (x : E) :
    Measurable (fun omega : ContinuousPath E ↦ incrementsMapE x (fun i ↦ omega (s i))) :=
  measurable_incrementsMapE.comp (measurable_const.prodMk
    (Measurable.of_eval fun i ↦ ContinuousPath.measurable_coordinateProcess (s i)))

/-- **The joint law of the increments of Brownian motion on `E` is a product of centred
Gaussians.** -/
theorem brownianMotionE_map_incrementsMap : ∀ {n : ℕ} {s : Fin n → ℝ≥0}, Monotone s → ∀ x : E,
    (brownianMotionE x).map (fun omega ↦ incrementsMapE x (fun i ↦ omega (s i))) =
      Measure.pi (fun i ↦ heatMeasure (0 : E) (timeIncrements s i)) := by
  intro n
  induction n with
  | zero =>
    intro s _ x
    exact (Measure.pi_eq fun A _ ↦ by simp).symm
  | succ n ih =>
    intro s hs x
    have hs' : Monotone (fun i : Fin n ↦ s i.succ - s 0) := fun a b hab ↦
      tsub_le_tsub_right (hs (Fin.succ_le_succ_iff.mpr hab)) _
    have hPhi : Measurable (fun p : E × ContinuousPath E ↦
        @Fin.cons n (fun _ : Fin (n + 1) ↦ E) (p.1 - x)
          (incrementsMapE p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) := by
      refine measurable_finCons.comp ((measurable_fst.sub measurable_const).prodMk ?_)
      exact measurable_incrementsMapE.comp (measurable_fst.prodMk
        (Measurable.of_eval fun i ↦
          (ContinuousPath.measurable_coordinateProcess (s i.succ - s 0)).comp measurable_snd))
    have hpair : Measurable (fun omega : ContinuousPath E ↦
        (omega (s 0), ContinuousPath.shift (s 0) omega)) :=
      (ContinuousPath.measurable_coordinateProcess (s 0)).prodMk
        (ContinuousPath.measurable_shift_fixed (s 0))
    have hfactor : (fun omega : ContinuousPath E ↦ incrementsMapE x (fun i ↦ omega (s i))) =
        (fun p : E × ContinuousPath E ↦
            @Fin.cons n (fun _ : Fin (n + 1) ↦ E) (p.1 - x)
              (incrementsMapE p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ∘
          (fun omega ↦ (omega (s 0), ContinuousPath.shift (s 0) omega)) := by
      funext omega
      have harg : (fun i : Fin n ↦ (ContinuousPath.shift (s 0) omega) (s i.succ - s 0)) =
          Fin.tail (fun i ↦ omega (s i)) := by
        funext i
        show omega (s 0 + (s i.succ - s 0)) = omega (s i.succ)
        rw [add_tsub_cancel_of_le (hs (Fin.zero_le _))]
      show incrementsMapE x (fun i ↦ omega (s i)) =
        Fin.cons (omega (s 0) - x)
          (incrementsMapE (omega (s 0))
            (fun i : Fin n ↦ (ContinuousPath.shift (s 0) omega) (s i.succ - s 0)))
      rw [incrementsMapE_succ, harg]
    rw [hfactor, ← Measure.map_map hPhi hpair, brownianMotionE_map_prodMk_shift]
    refine (Measure.pi_eq fun A hA ↦ ?_).symm
    have hpiA : MeasurableSet (Set.univ.pi A) := MeasurableSet.univ_pi hA
    rw [Measure.map_apply hPhi hpiA, Measure.compProd_apply (hPhi hpiA)]
    have hsplit : ∀ y : E, brownianMotionE y (Prod.mk y ⁻¹'
          ((fun p : E × ContinuousPath E ↦
            @Fin.cons n (fun _ : Fin (n + 1) ↦ E) (p.1 - x)
              (incrementsMapE p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) =
        Set.indicator ((fun u : E ↦ u - x) ⁻¹' (A 0))
          (fun _ ↦ ∏ i : Fin n,
            heatMeasure (0 : E) (timeIncrements (fun i : Fin n ↦ s i.succ - s 0) i) (A i.succ)) y := by
      intro y
      have hmem : ∀ eta : ContinuousPath E,
          (Prod.mk y eta ∈ ((fun p : E × ContinuousPath E ↦
              @Fin.cons n (fun _ : Fin (n + 1) ↦ E) (p.1 - x)
                (incrementsMapE p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) ↔
            (y - x ∈ A 0 ∧
              incrementsMapE y (fun i : Fin n ↦ eta (s i.succ - s 0)) ∈
                Set.univ.pi (fun i : Fin n ↦ A i.succ)) := by
        intro eta
        simp only [Set.mem_preimage, Set.mem_univ_pi]
        rw [Fin.forall_fin_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
      by_cases hy : y - x ∈ A 0
      · have hy' : y ∈ (fun u : E ↦ u - x) ⁻¹' (A 0) := hy
        rw [Set.indicator_of_mem hy']
        have hset : (Prod.mk y ⁻¹'
            ((fun p : E × ContinuousPath E ↦
              @Fin.cons n (fun _ : Fin (n + 1) ↦ E) (p.1 - x)
                (incrementsMapE p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) =
            (fun eta : ContinuousPath E ↦
              incrementsMapE y (fun i : Fin n ↦ eta (s i.succ - s 0))) ⁻¹'
              (Set.univ.pi (fun i : Fin n ↦ A i.succ)) := by
          ext eta
          rw [Set.mem_preimage, hmem eta]
          simp only [Set.mem_preimage, hy, true_and]
        rw [hset, ← Measure.map_apply
          (measurable_incrementsMapE_eval (fun i : Fin n ↦ s i.succ - s 0) y)
          (MeasurableSet.univ_pi fun i ↦ hA i.succ), ih hs' y, Measure.pi_pi]
      · have hy' : y ∉ (fun u : E ↦ u - x) ⁻¹' (A 0) := hy
        rw [Set.indicator_of_notMem hy']
        have hset : (Prod.mk y ⁻¹'
            ((fun p : E × ContinuousPath E ↦
              @Fin.cons n (fun _ : Fin (n + 1) ↦ E) (p.1 - x)
                (incrementsMapE p.1 (fun i : Fin n ↦ p.2 (s i.succ - s 0)))) ⁻¹' Set.univ.pi A)) =
            (∅ : Set (ContinuousPath E)) := by
          ext eta
          rw [Set.mem_preimage, hmem eta]
          simp only [Set.mem_empty_iff_false, iff_false, not_and, hy, IsEmpty.forall_iff]
        rw [hset, measure_empty]
    have hsub : Measurable (fun u : E ↦ u - x) := by fun_prop
    simp_rw [hsplit]
    rw [lintegral_indicator (hsub (hA 0)), setLIntegral_const,
      ← Measure.map_apply hsub (hA 0),
      heatMeasure_map_sub_const x, Fin.prod_univ_succ, timeIncrements_zero_apply]
    exact mul_comm _ _

end Increments

section IndependentIncrements

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Dropping the first coordinate of a finite coordinate path in `E` is measurable. -/
theorem measurable_finTailE {n : ℕ} :
    Measurable (Fin.tail : (Fin (n + 1) → E) → (Fin n → E)) :=
  Measurable.of_eval fun i ↦ measurable_pi_apply i.succ

omit [BorelSpace E] in
/-- Dropping the first coordinate of a product of probability measures gives the product of the
remaining ones. -/
theorem map_finTailE_pi {n : ℕ} (nu : Fin (n + 1) → Measure E)
    [∀ i, IsProbabilityMeasure (nu i)] :
    (Measure.pi nu).map Fin.tail = Measure.pi (fun i : Fin n ↦ nu i.succ) := by
  refine (Measure.pi_eq fun A hA ↦ ?_).symm
  have hpre : (Fin.tail : (Fin (n + 1) → E) → (Fin n → E)) ⁻¹' (Set.univ.pi A)
      = Set.univ.pi (@Fin.cons n (fun _ ↦ Set E) Set.univ A) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    rw [Fin.forall_fin_succ]
    simp [Fin.tail]
  rw [Measure.map_apply measurable_finTailE (MeasurableSet.univ_pi hA), hpre, Measure.pi_pi,
    Fin.prod_univ_succ]
  simp

/-- **The increments of Brownian motion on `E` over a monotone family of times are independent
centred Gaussians.** -/
theorem brownianMotionE_map_increments {n : ℕ} {t : Fin (n + 1) → ℝ≥0} (ht : Monotone t)
    (x : E) :
    (brownianMotionE x).map
        (fun (omega : ContinuousPath E) (i : Fin n) ↦ omega (t i.succ) - omega (t i.castSucc)) =
      Measure.pi (fun i : Fin n ↦ heatMeasure (0 : E) (t i.succ - t i.castSucc)) := by
  have hfac : (fun (omega : ContinuousPath E) (i : Fin n) ↦
      omega (t i.succ) - omega (t i.castSucc)) =
      Fin.tail ∘ (fun omega ↦ incrementsMapE x (fun i ↦ omega (t i))) := by
    funext omega i
    exact (incrementsMapE_succ_apply x (fun j ↦ omega (t j)) i).symm
  rw [hfac, ← Measure.map_map measurable_finTailE (measurable_incrementsMapE_eval t x),
    brownianMotionE_map_incrementsMap ht x, map_finTailE_pi]
  congr 1
  funext i
  rw [timeIncrements_succ_apply ht i]

/-- Every increment of Brownian motion on `E` is a centred Gaussian of covariance the elapsed
time times the identity. -/
theorem brownianMotionE_map_increment (x : E) (a b : ℝ≥0) (hab : a ≤ b) :
    (brownianMotionE x).map (fun omega ↦ omega b - omega a) = heatMeasure (0 : E) (b - a) := by
  have ht : Monotone (![a, b]) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := brownianMotionE_map_increments (n := 1) (t := ![a, b]) ht x
  have hmeas : Measurable (fun (omega : ContinuousPath E) (i : Fin 1) ↦
      omega ((![a, b] : Fin 2 → ℝ≥0) i.succ) - omega ((![a, b] : Fin 2 → ℝ≥0) i.castSucc)) :=
    Measurable.of_eval fun i ↦
      (ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _)
  have hproj := congrArg (fun mu : Measure (Fin 1 → E) ↦ mu.map (Function.eval (0 : Fin 1))) h
  have hpres := measurePreserving_eval (fun i : Fin 1 ↦ heatMeasure (0 : E)
    ((![a, b] : Fin 2 → ℝ≥0) i.succ - (![a, b] : Fin 2 → ℝ≥0) i.castSucc)) 0
  rw [Measure.map_map (measurable_pi_apply _) hmeas, hpres.map_eq] at hproj
  exact hproj

/-- **Brownian motion on `E` has independent increments.** -/
theorem hasIndepIncrements_brownianMotionE (x : E) :
    HasIndepIncrements (fun (t : ℝ≥0) (omega : ContinuousPath E) ↦ omega t - x)
      (brownianMotionE x) := by
  intro n t ht
  have hsimp : (fun (i : Fin n) (omega : ContinuousPath E) ↦
      (omega (t i.succ) - x) - (omega (t i.castSucc) - x)) =
      fun (i : Fin n) (omega : ContinuousPath E) ↦ omega (t i.succ) - omega (t i.castSucc) := by
    funext i omega
    abel
  show iIndepFun (fun (i : Fin n) (omega : ContinuousPath E) ↦
    (omega (t i.succ) - x) - (omega (t i.castSucc) - x)) (brownianMotionE x)
  rw [hsimp]
  have hmeasi : ∀ i : Fin n, Measurable (fun omega : ContinuousPath E ↦
      omega (t i.succ) - omega (t i.castSucc)) := fun i ↦
    (ContinuousPath.measurable_coordinateProcess _).sub
      (ContinuousPath.measurable_coordinateProcess _)
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i ↦ (hmeasi i).aemeasurable),
    brownianMotionE_map_increments ht x]
  congr 1
  funext i
  exact (brownianMotionE_map_increment x _ _ (ht (Fin.castSucc_lt_succ (i := i)).le)).symm

end IndependentIncrements

section Identification

/-- A process in `E` is a Brownian motion when its one-time marginals are the centred Gaussians
of covariance the elapsed time times the identity, it has independent increments, and almost
every path is continuous.

This is the finite-dimensional counterpart of `IsBrownianReal` of
`Examples.BrownianMotion`, stated through Gaussian marginals and independent increments rather
than through a projective family. -/
structure IsBrownianE {Omega : Type*} [MeasurableSpace Omega]
    (X : ℝ≥0 → Omega → E) (P : Measure Omega) : Prop where
  /-- At every time the value has the centred Gaussian law of covariance that time. -/
  hasLaw_eval : ∀ t : ℝ≥0, HasLaw (X t) (heatMeasure (0 : E) t) P
  /-- The increments over disjoint consecutive intervals are independent. -/
  hasIndepIncrements : HasIndepIncrements X P
  /-- Almost every trajectory is continuous. -/
  cont : ∀ᵐ omega ∂P, Continuous fun t ↦ X t omega

/-- **The canonical process under `brownianMotionE x`, recentred at its starting point, is a
Brownian motion on `E`.** -/
theorem isBrownianE_brownianMotionE (x : E) :
    IsBrownianE (fun (t : ℝ≥0) (omega : ContinuousPath E) ↦ omega t - x)
      (brownianMotionE x) where
  hasLaw_eval t := by
    refine ⟨((ContinuousPath.measurable_coordinateProcess t).sub measurable_const).aemeasurable, ?_⟩
    have hmeas : Measurable (fun omega : ContinuousPath E ↦ omega t) :=
      ContinuousPath.measurable_coordinateProcess t
    have hsub : Measurable (fun u : E ↦ u - x) := by fun_prop
    rw [show (fun omega : ContinuousPath E ↦ omega t - x)
        = (fun u : E ↦ u - x) ∘ (fun omega : ContinuousPath E ↦ omega t) from rfl,
      ← Measure.map_map hsub hmeas, brownianMotionE_map_eval, heatMeasure_map_sub_const x]
  hasIndepIncrements := hasIndepIncrements_brownianMotionE x
  cont := Filter.Eventually.of_forall fun omega ↦ omega.continuous.sub continuous_const

end Identification

end

end MarkovProcess
