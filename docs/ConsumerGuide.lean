/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Main
import MarkovProcess.Analysis.PaleyZygmund
import MarkovProcess.Path.ExitTime
import MarkovProcess.Path.Sampling
import MarkovProcess.Killed.Kernel
import MarkovProcess.Killed.Marginals
import MarkovProcess.Killed.Nested
import MarkovProcess.Killed.ExitTimeIdentification
import MarkovProcess.Trajectory.DiscountedDynkin
import MarkovProcess.Trajectory.Dynkin
import MarkovProcess.Trajectory.DynkinStopping
import MarkovProcess.Trajectory.ExitTimeExponentialMoment
import MarkovProcess.Trajectory.ExitTimeLaplace
import MarkovProcess.Trajectory.ExcessiveStopping
import MarkovProcess.Trajectory.FeynmanKac
import MarkovProcess.Trajectory.ResolventExitDecomposition
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
import MarkovProcess.Kernel.OnePointExtension
import MarkovProcess.Kernel.OnePointKilled
import MarkovProcess.Kernel.OnePointKolmogorov
import MarkovProcess.Semigroup.GeneratorResolvent
import MarkovProcess.Semigroup.GeneratorUniqueness
import MarkovProcess.Semigroup.ExponentialComparison
import MarkovProcess.Semigroup.ResolventGeneration
import MarkovProcess.Feller.Resolvent
import MarkovProcess.Semigroup.TrotterKato
import MarkovProcess.Trajectory.Convergence
import MarkovProcess.Trajectory.WeakConvergence
import MarkovProcess.Killed.GluingC0
import MarkovProcess.Examples.HeatOnePoint

/-!
# Consumer guide probe

The consumer guide's code blocks, verbatim, so that the guide is checked against the
library: `scripts/check_docs.sh` compiles this file (it is not part of the built library).
Every block is an `example`, so this file adds no declarations.
-/

open MeasureTheory ProbabilityTheory MarkovProcess SubMarkovKernelSemigroup
open scoped BoundedContinuousFunction ENNReal NNReal ZeroAtInfty

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [SecondCountableTopology alpha]
  [LocallyCompactSpace alpha] [Nonempty alpha] [MeasurableSpace alpha] [BorelSpace alpha]
variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
  (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M)

example : ∃! Q : Kernel alpha (ContinuousPath alpha), IsMarkovKernel Q ∧
    ∀ I : Finset NNReal, Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I :=
  hFeller.existsUnique_continuousProcess_of_hasKolmogorovMoments P hP hmom

noncomputable example : Kernel alpha (ContinuousPath alpha) :=
  IsConservative.continuousProcess P hP

example : IsMarkovKernel (IsConservative.continuousProcess P hP) := inferInstance

example : P.KolmogorovRegular hP := KolmogorovRegular.of_hasKolmogorovMoments P hP hmom

example (I : Finset NNReal) :
    (IsConservative.continuousProcess P hP).map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel P I :=
  hFeller.continuousProcess_map_finiteEvaluation P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) I

example : (IsConservative.continuousProcess P hP).map (fun omega ↦ omega 0) = Kernel.id :=
  IsConservative.continuousProcess_map_eval_zero P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)

example (t : NNReal) (g : BoundedContinuousFunction alpha ℝ) :
    Continuous fun x ↦ ∫ omega, g (omega t) ∂(IsConservative.continuousProcess P hP x) :=
  hFeller.continuous_integral_eval_continuousProcess P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) t g

example (s : NNReal) :
    (IsConservative.continuousProcess P hP).map (ContinuousPath.shift s) =
      (IsConservative.continuousProcess P hP).comp (P s) :=
  hFeller.continuousProcess_map_shift P hP (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) s

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

example (U : Set alpha) (hU : IsOpen U) (x : alpha)
    (F : ContinuousPath alpha → ℝ) (hF : StronglyMeasurable F) (C : ℝ)
    (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    ((IsConservative.continuousProcess P hP) x)[
        {omega | ContinuousPath.exitTime U omega < ⊤}.indicator fun omega ↦
          F (ContinuousPath.shift ((ContinuousPath.exitTime U omega).untopD 0) omega) |
        (ContinuousPath.isStoppingTime_exitTime U hU).measurableSpace] =ᵐ[
      (IsConservative.continuousProcess P hP) x]
      {omega | ContinuousPath.exitTime U omega < ⊤}.indicator fun omega ↦
        ∫ eta, F eta ∂(IsConservative.continuousProcess P hP)
          (omega ((ContinuousPath.exitTime U omega).untopD 0)) :=
  hFeller.continuousProcess_condExp_shift_stoppingTime_lt_top P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) x (ContinuousPath.exitTime U)
    (ContinuousPath.isStoppingTime_exitTime U hU) F hF C hFC

example (Q : Kernel alpha (ContinuousPath alpha)) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) :
    Q = IsConservative.continuousProcess P hP :=
  IsConservative.eq_continuousProcess_of_map_finiteEvaluation P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) Q hQ

example (U : Set alpha) (hU : IsOpen U) (lam : ℝ) (hlam : 0 < lam) (x : alpha) :
    ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal
          (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal))) omega
        ∂(IsConservative.continuousProcess P hP x) =
      1 - ENNReal.ofReal lam *
        IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) x :=
  hP.lintegral_exp_neg_exitTime P U hU lam hlam x

example (U : Set alpha) (hU : IsOpen U) (M0 : ℝ≥0)
    (hM : ∀ y, ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP y) ≤ (M0 : ℝ≥0∞))
    (lam : ℝ) (hlam : 0 ≤ lam) (hrate : Real.exp (lam * (2 * (M0 : ℝ))) < 2) (x : alpha) :
    ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
        ∂(IsConservative.continuousProcess P hP x)
      ≤ ENNReal.ofReal (Real.exp (lam * (2 * (M0 : ℝ)))) *
        (1 - 2⁻¹ * ENNReal.ofReal (Real.exp (lam * (2 * (M0 : ℝ)))))⁻¹ :=
  hP.lintegral_exponentialStoppingWeight_exitTime_le_of_lintegral_le P hFeller
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) U hU M0 hM lam hlam hrate x

example (U : Set alpha) (hU : IsOpen U) (M0 K0 : ℝ≥0) (hK0 : 1 < K0)
    (hM : ∀ y, ∫⁻ omega, ContinuousPath.exitTime U omega
      ∂(IsConservative.continuousProcess P hP y) ≤ (M0 : ℝ≥0∞))
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hrate : Real.exp (lam * ((K0 : ℝ) * (M0 : ℝ))) * ((K0 : ℝ) + 2) ≤ 2 * (K0 : ℝ))
    (x : alpha) :
    ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
        ∂(IsConservative.continuousProcess P hP x) ≤ 2 :=
  hP.lintegral_exponentialStoppingWeight_exitTime_le_two_of_lintegral_le P hFeller
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) U hU M0 hM K0 hK0 lam hlam hrate x

example (U : Set alpha) (lam : ℝ) (hlam : 0 < lam) (p0 : ℕ) (x : alpha) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ^ p0
        ∂(IsConservative.continuousProcess P hP x)
      ≤ ENNReal.ofReal (((p0 : ℝ) / (lam * Real.exp 1)) ^ p0) *
        ∫⁻ omega, ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime U) omega
          ∂(IsConservative.continuousProcess P hP x) :=
  hP.lintegral_exitTime_pow_le P U lam hlam p0 x

example (U : Set alpha) (hU : IsOpen U) (x : alpha) (rho : ℝ≥0)
    (hsq : ∫⁻ omega, ContinuousPath.exitTime U omega ^ 2
      ∂(IsConservative.continuousProcess P hP x) ≠ ⊤) :
    ((1 : ℝ≥0∞) - rho) ^ 2 * (∫⁻ omega, ContinuousPath.exitTime U omega
          ∂(IsConservative.continuousProcess P hP x)) ^ 2 /
        (∫⁻ omega, ContinuousPath.exitTime U omega ^ 2
          ∂(IsConservative.continuousProcess P hP x)) ≤
      IsConservative.continuousProcess P hP x
        {omega | (rho : ℝ≥0∞) * ∫⁻ eta, ContinuousPath.exitTime U eta
            ∂(IsConservative.continuousProcess P hP x) ≤ ContinuousPath.exitTime U omega} :=
  le_measure_ge_of_lintegral_sq_ne_top _ (ContinuousPath.measurable_exitTime U hU) hsq rho

example (U : Set alpha) (omega : ContinuousPath alpha) (T : NNReal)
    (hT : (T : ℝ≥0∞) < ContinuousPath.exitTime U omega) (h : ℝ) (hh : 0 < h) :
    ∃ M : ℕ, 0 < M ∧
      (∀ k ≤ M, (((k : NNReal) * T / (M : NNReal) : NNReal) : ℝ≥0∞) <
        ContinuousPath.exitTime U omega) ∧
      ∀ k < M, dist (omega ((k : NNReal) * T / (M : NNReal)))
        (omega (((k : NNReal) + 1) * T / (M : NNReal))) < h :=
  ContinuousPath.exists_uniform_sampling_lt_exitTime U omega T hT h hh

example (v : C₀(alpha, ℝ)) (lam : ℝ)
    (hv : P.IsLambdaExcessive lam v) (U : Set alpha) (hU : IsOpen U) (x : alpha) :
    ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦
          ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
            ENNReal.ofReal (v (omega ((ContinuousPath.exitTime U omega).untopD 0)))) omega
        ∂(IsConservative.continuousProcess P hP x) ≤ ENNReal.ofReal (v x) :=
  hv.lintegral_discountedValue_exitTime_le hP hFeller
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) U hU x

example (f : C₀(ℝ, ℝ)) (hf : ∀ y, 0 ≤ f y) (lam : ℝ) (hlam : 0 < lam)
    (U : Set ℝ) (hU : IsOpen U) (x : ℝ) :
    let v := isFellerKernelSemigroup_heatSemigroup.c0Semigroup.resolvent
      (⟨lam, hlam⟩ : Semigroup.PositiveShift) f
    ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦
          ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
            ENNReal.ofReal (v (omega ((ContinuousPath.exitTime U omega).untopD 0)))) omega
        ∂(IsConservative.continuousProcess heatSemigroup isConservative_heatSemigroup x) ≤
      ENNReal.ofReal (v x) := by
  dsimp only
  exact (isFellerKernelSemigroup_heatSemigroup.resolvent_isLambdaExcessive
    lam hlam f hf).lintegral_discountedValue_exitTime_le isConservative_heatSemigroup
      isFellerKernelSemigroup_heatSemigroup kolmogorovRegular_heatSemigroup U hU x

example {q : alpha → ℝ} (hq : Measurable q) (U : Set alpha) (hU : IsOpen U)
    (hqU : ∀ y ∈ U, q y = 0) (lam : ℝ) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x ≤
      IsConservative.feynmanKacResolvent P hP q lam f x :=
  hP.killedResolvent_le_feynmanKacResolvent P hq hU hqU lam hf x

example (lam : ℝ) (f : alpha → ℝ≥0∞) (hf : Measurable f) (x : alpha) :
    ∫⁻ omega, ContinuousPath.pathResolvent lam f omega
        ∂(IsConservative.continuousProcess P hP x) =
      IsConservative.killedResolvent P hP Set.univ isOpen_univ lam f x :=
  hP.lintegral_pathResolvent_eq_killedResolvent_univ P lam hf x

example (U : Set alpha) (hU : IsOpen U) (lam : ℝ)
    (hK : P.KolmogorovRegular hP) (f : alpha → ℝ≥0∞) (hf : Measurable f) (x : alpha) :
    ∫⁻ omega, ContinuousPath.pathResolvent lam f omega
        ∂(IsConservative.continuousProcess P hP x) =
      IsConservative.killedResolvent P hP U hU lam f x +
        ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
          (fun omega ↦ ENNReal.ofReal
              (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
            (∫⁻ eta, ContinuousPath.pathResolvent lam f eta
              ∂(IsConservative.continuousProcess P hP
                (omega ((ContinuousPath.exitTime U omega).untopD 0))))) omega
          ∂(IsConservative.continuousProcess P hP x) :=
  hFeller.lintegral_pathResolvent_eq_killedResolvent_add P hP hK U hU lam hf x

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

example {potential : alpha → ℝ} (hpotential : Measurable potential) {C : ℝ}
    (hpotential0 : ∀ y, 0 ≤ potential y) (hpotentialC : ∀ y, potential y ≤ C)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) {D : NNReal}
    (hfD : ∀ y, f y ≤ (D : ℝ≥0∞)) (lam : ℝ) (hlam : 0 < lam) (x : alpha) :
    IsConservative.feynmanKacResolvent P hP potential lam f x =
      P.kernelResolvent lam f x -
        P.kernelResolvent lam (fun y ↦ ENNReal.ofReal (potential y) *
          IsConservative.feynmanKacResolvent P hP potential lam f y) x :=
  hFeller.feynmanKacResolvent_eq_kernelResolvent_sub P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)
    hpotential hpotential0 hpotentialC hf hfD lam hlam x

example (potential : alpha → ℝ) {f : alpha → ℝ} (hf : Measurable f) :
    IsConservative.feynmanKac P hP potential 0 f = f :=
  hP.feynmanKac_zero P (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) potential hf

example (t : NNReal) (x : alpha) {f : alpha → ℝ} (hf : Measurable f) :
    ∫ omega, f (omega t) ∂(IsConservative.continuousProcess P hP x) =
      ∫ y, f y ∂(P t x) :=
  hFeller.integral_eval_continuousProcess_of_measurable P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) t x hf

example (t : NNReal) :
    Measurable[(borel ℝ).prod (ContinuousPath.canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦ p.2 (min (Real.toNNReal p.1) t)) :=
  ContinuousPath.measurable_clampedCoordinate t

example {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ s in Set.Ioo (0 : ℝ) t, h (s, t - s)) =
      ∫⁻ s in Set.Ioi (0 : ℝ), ∫⁻ u in Set.Ioi (0 : ℝ), h (s, u) :=
  intervalIntegral.lintegral_timeTriangle_sub hh

example (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    P.kernelResolvent lam f x =
      IsConservative.killedResolvent P hP Set.univ isOpen_univ lam f x :=
  hFeller.kernelResolvent_eq_killedResolvent_univ P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) lam hf x

example (mu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ))
    (hf0 : ∀ y, 0 ≤ f y) (x : alpha) :
    P.kernelResolvent (mu : ℝ) (fun y ↦ ENNReal.ofReal (f y)) x =
      ENNReal.ofReal (hFeller.c0Semigroup.resolvent mu f x) :=
  hFeller.kernelResolvent_ofReal_eq_resolvent mu f hf0 x

example {potential : alpha → ℝ} (hpotential : Measurable potential) {C : ℝ}
    (hpotential0 : ∀ y, 0 ≤ potential y) (hpotentialC : ∀ y, potential y ≤ C)
    {mu lam : ℝ} (hmu : 0 < mu) (hlam : 0 < lam) {f : alpha → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    IsConservative.feynmanKacResolventReal P hP potential mu f =
      IsConservative.feynmanKacResolventReal P hP potential lam f +
        (lam - mu) • IsConservative.feynmanKacResolventReal P hP potential lam
          (IsConservative.feynmanKacResolventReal P hP potential mu f) :=
  hFeller.feynmanKacResolventReal_resolvent_identity P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)
    hpotential hpotential0 hpotentialC hmu hlam hf hfD

example {potential : alpha → ℝ} (hpotential : Measurable potential) {C : ℝ}
    (hpotential0 : ∀ y, 0 ≤ potential y) (hpotentialC : ∀ y, potential y ≤ C)
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    IsConservative.feynmanKacResolventReal P hP potential lam f =
      P.kernelResolventReal lam f - P.kernelResolventReal lam
        (fun y ↦ potential y *
          IsConservative.feynmanKacResolventReal P hP potential lam f y) :=
  hFeller.feynmanKacResolventReal_perturbation P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)
    hpotential hpotential0 hpotentialC hlam hf hfD

example {U : Set alpha} (hU : IsOpen U) (hK : P.KolmogorovRegular hP)
    {potential : alpha → ℝ}
    (hpotential : Measurable potential) (hpotentialU : ∀ y ∈ U, potential y = 0)
    {C : ℝ} (hpotential0 : ∀ y, 0 ≤ potential y) (hpotentialC : ∀ y, potential y ≤ C)
    (Y : ℝ → (alpha → ℝ) → alpha → ℝ)
    (hY_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f))
    (hY_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D)
    (hY_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f))
    (hY_perturbation : ∀ {lam : ℝ}, C < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y lam f = P.kernelResolventReal lam f -
        P.kernelResolventReal lam (fun y ↦ potential y * Y lam f y))
    {f : alpha → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam (fun y ↦ ENNReal.ofReal (f y)) x ≤
      ENNReal.ofReal (Y lam f x) :=
  hFeller.killedResolvent_le_of_perturbed_resolventFamily P hP
    hK hU hpotential hpotentialU hpotential0 hpotentialC Y hY_meas hY_bound
    hY_resolvent hY_perturbation
    hf hf0 hfD hlam x

example (R X Y : (alpha → ℝ) → alpha → ℝ) {potential : alpha → ℝ}
    {C lam : ℝ}
    (hR_add : ∀ {f g : alpha → ℝ}, Measurable f → Measurable g →
      (∃ D, ∀ x, |f x| ≤ D) → (∃ D, ∀ x, |g x| ≤ D) → R (f + g) = R f + R g)
    (hR_bound : ∀ {f : alpha → ℝ}, Measurable f → ∀ {D : ℝ},
      (∀ x, |f x| ≤ D) → ∀ x, |R f x| ≤ D / lam)
    (hpotential : Measurable potential) (hpotential0 : ∀ x, 0 ≤ potential x)
    (hpotentialC : ∀ x, potential x ≤ C) (hlam : C < lam)
    (hX_meas : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Measurable (X f))
    (hY_meas : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Measurable (Y f))
    (hX_bound : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      ∃ D, ∀ x, |X f x| ≤ D)
    (hY_bound : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      ∃ D, ∀ x, |Y f x| ≤ D)
    (hX_fixed : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X f = R f - R (fun x ↦ potential x * X f x))
    (hY_fixed : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y f = R f - R (fun x ↦ potential x * Y f x))
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    X f = Y f :=
  MarkovProcess.perturbed_unique R X Y hR_add hR_bound hpotential hpotential0
    hpotentialC hlam hX_meas hY_meas hX_bound hY_bound hX_fixed hY_fixed hf hfD

example (X Y : ℝ → (alpha → ℝ) → alpha → ℝ) (C : ℝ)
    (hX_add : ∀ {lam : ℝ}, 0 < lam → ∀ {f g : alpha → ℝ},
      Measurable f → Measurable g → (∃ D, ∀ x, |f x| ≤ D) →
      (∃ D, ∀ x, |g x| ≤ D) → X lam (f + g) = X lam f + X lam g)
    (hX_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (X lam f))
    (hY_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f))
    (hX_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      ∀ {D : ℝ}, (∀ x, |f x| ≤ D) → ∀ x, |X lam f x| ≤ D / lam)
    (hY_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D)
    (hX_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X mu f = X lam f + (lam - mu) • X lam (X mu f))
    (hY_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f))
    (hlarge : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {g : alpha → ℝ}, Measurable g →
      (∃ D, ∀ x, |g x| ≤ D) → X lam g = Y lam g) {mu : ℝ} (hmu : 0 < mu)
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    X mu f = Y mu f :=
  MarkovProcess.resolventFamily_eq_of_eventually X Y C hX_add hX_meas hY_meas
    hX_bound hY_bound hX_resolvent hY_resolvent hlarge hmu hf hfD

example (R X Y : ℝ → (alpha → ℝ) → alpha → ℝ) {potential : alpha → ℝ} {C : ℝ}
    (hR_add : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f g : alpha → ℝ},
      Measurable f → Measurable g → (∃ D, ∀ x, |f x| ≤ D) →
      (∃ D, ∀ x, |g x| ≤ D) → R lam (f + g) = R lam f + R lam g)
    (hR_bound : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → ∀ {D : ℝ}, (∀ x, |f x| ≤ D) →
      ∀ x, |R lam f x| ≤ D / lam)
    (hpotential : Measurable potential) (hpotential0 : ∀ x, 0 ≤ potential x)
    (hpotentialC : ∀ x, potential x ≤ C)
    (hX_add : ∀ {lam : ℝ}, 0 < lam → ∀ {f g : alpha → ℝ},
      Measurable f → Measurable g → (∃ D, ∀ x, |f x| ≤ D) →
      (∃ D, ∀ x, |g x| ≤ D) → X lam (f + g) = X lam f + X lam g)
    (hX_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (X lam f))
    (hY_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f))
    (hX_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      ∀ {D : ℝ}, (∀ x, |f x| ≤ D) → ∀ x, |X lam f x| ≤ D / lam)
    (hY_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D)
    (hX_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X mu f = X lam f + (lam - mu) • X lam (X mu f))
    (hY_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f))
    (hX_fixed : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X lam f = R lam f - R lam (fun x ↦ potential x * X lam f x))
    (hY_fixed : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y lam f = R lam f - R lam (fun x ↦ potential x * Y lam f x))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) : X lam f = Y lam f :=
  MarkovProcess.perturbed_eq_of_resolventFamilies R X Y hR_add hR_bound hpotential
    hpotential0 hpotentialC hX_add hX_meas hY_meas hX_bound hY_bound hX_resolvent
    hY_resolvent hX_fixed hY_fixed hlam hf hfD

example (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    (K : NNReal) (lam : ℝ) (x : alpha) :
    ∫ omega, Real.exp (-lam * (ContinuousPath.exitTimeTrunc U K omega : ℝ)) *
          (f : C₀(alpha, ℝ)) (omega (ContinuousPath.exitTimeTrunc U K omega))
        ∂(IsConservative.continuousProcess P hP x) - (f : C₀(alpha, ℝ)) x =
      ∫ omega, (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc U K omega : ℝ),
          Real.exp (-lam * s) *
            (hFeller.c0Semigroup.generator f - lam • (f : C₀(alpha, ℝ)))
              (omega (Real.toNNReal s)))
        ∂(IsConservative.continuousProcess P hP x) :=
  hFeller.integral_exp_eval_exitTimeTrunc_sub_eq_integral_integral hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) f U hU K lam x

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

example (U : Set alpha) (hU : IsOpen U) (x : alpha) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ∂(IsConservative.continuousProcess P hP x) =
      IsConservative.killedResolvent P hP U hU 0 (fun _ ↦ 1) x :=
  IsConservative.lintegral_exitTime_eq_killedResolvent_zero P hP U hU x

example (U : Set alpha) (hU : IsOpen U) (RU : ℝ → alpha → ℝ≥0∞) (w : alpha → ℝ≥0∞)
    (hident : ∀ lam : ℝ, 0 < lam → ∀ y ∈ U,
      IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) y = RU lam y)
    (hlim : ∀ y ∈ U, ⨆ n : ℕ, RU ((n : ℝ) + 1)⁻¹ y = w y)
    (M0 : ℝ≥0∞) (hupper : ∀ y ∈ U, w y ≤ M0) {x : alpha} (hx : x ∈ U) :
    ∫⁻ omega, ContinuousPath.exitTime U omega
        ∂(IsConservative.continuousProcess P hP x) ≤ M0 :=
  IsConservative.lintegral_exitTime_le_of_killedResolvent_eq P hP RU w U hU hident hlim M0
    hupper hx

example (U : Set alpha) (hU : IsOpen U) (RU : ℝ → alpha → ℝ≥0∞) (w : alpha → ℝ≥0∞)
    (hident : ∀ lam : ℝ, 0 < lam → ∀ y ∈ U,
      IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) y = RU lam y)
    (hw : ∀ y ∈ U, Filter.Tendsto (fun lam : ℝ ↦ RU lam y)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (w y)))
    {x : alpha} (hx : x ∈ U) :
    ∫⁻ omega, ContinuousPath.exitTime U omega
        ∂(IsConservative.continuousProcess P hP x) = w x :=
  IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq P hP RU w U hU hident
    (IsConservative.iSup_eq_of_tendsto_nhdsGT_zero P hP RU w U hU hident hw) hx

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

noncomputable example : PositiveC0ContractiveResolvent alpha :=
  hFeller.positiveC0ContractiveResolvent

example (μ : Semigroup.PositiveShift) :
    R.isFellerKernelSemigroup_kernelSemigroup.c0Semigroup.resolvent μ =
      R.toContractiveResolvent.operator μ :=
  R.resolvent_c0Semigroup_kernelSemigroup μ

noncomputable example : PositiveC0ContractiveResolvent (OnePoint alpha) :=
  R.onePointResolvent

example : R.onePointKernelSemigroup.IsConservative :=
  R.isConservative_onePointKernelSemigroup

example (t : NNReal) :
    R.onePointKernelSemigroup t OnePoint.infty = Measure.dirac OnePoint.infty :=
  R.onePointKernelSemigroup_absorbing t

section OnePointRegularity

-- An explicit positive, bounded, `1`-Lipschitz exhaustion with compact positive superlevels
-- selects the metric used by both the tail criterion and the one-point process.
variable (rho : alpha → ℝ) (hrho_cont : Continuous rho) (hrho_pos : ∀ x, 0 < rho x)
  (hrho_lipschitz : LipschitzWith 1 rho)
  (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
  {pOne qOne : ℝ} {MOne BOne : ℝ≥0}
  {phi : ℝ≥0 → alpha → ℝ → ℝ≥0∞}
  (htail : R.onePointKernelSemigroup.HasOnePointTailBounds
    rho hrho_cont hrho_pos hrho_lipschitz hrho_compact pOne qOne MOne BOne phi)

example (h : NNReal) (x : alpha) (r : ℝ) (C : ℝ≥0∞)
    (hlive : R.kernelSemigroup h x {y | r < dist y x} ≤ C)
    (hcemetery : R.onePointKernelSemigroup h (x : OnePoint alpha) {OnePoint.infty} =
      1 - R.kernelSemigroup h x Set.univ) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    R.onePointKernelSemigroup h (x : OnePoint alpha)
        {z | r < dist z (x : OnePoint alpha)} ≤
      C + (1 - R.kernelSemigroup h x Set.univ) :=
  R.onePointKernelSemigroup_tail_le_of_tail_le rho hrho_cont hrho_pos hrho_lipschitz
    hrho_compact h x r C hlive hcemetery

example (h : NNReal) (x : alpha) (r A theta : ℝ) (v : C₀(OnePoint alpha, ℝ))
    (hA : 0 < A) (hv_nonneg : ∀ z, 0 ≤ v z)
    (hmajorant : ∀ z, r < OnePoint.exhaustionDist rho z (x : OnePoint alpha) → A ≤ v z)
    (hintegral : ∫ z, v z ∂R.onePointKernelSemigroup h (x : OnePoint alpha) ≤
      Real.exp (theta * (h : ℝ)) * v (x : OnePoint alpha)) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    R.onePointKernelSemigroup h (x : OnePoint alpha)
        {z | r < dist z (x : OnePoint alpha)} ≤
      ENNReal.ofReal (Real.exp (theta * (h : ℝ)) * v (x : OnePoint alpha) / A) :=
  R.onePointKernelSemigroup.measure_gt_le_of_le_c0 rho hrho_cont hrho_pos hrho_lipschitz
    hrho_compact h x r A theta v hA hv_nonneg hmajorant hintegral

example :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    R.onePointKernelSemigroup.KolmogorovRegular
    R.isConservative_onePointKernelSemigroup :=
  R.kolmogorovRegular_onePointKernelSemigroup rho hrho_cont hrho_pos hrho_lipschitz
    hrho_compact htail

noncomputable example :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint alpha) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    Kernel (OnePoint alpha) (ContinuousPath (OnePoint alpha)) :=
  letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  letI : CompleteSpace (OnePoint alpha) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  IsConservative.continuousProcess R.onePointKernelSemigroup
    R.isConservative_onePointKernelSemigroup

example (x : alpha) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint alpha) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    ∀ᵐ omega ∂IsConservative.continuousProcess R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup (x : OnePoint alpha),
      ContinuousPath.exitTime (Set.range ((↑) : alpha → OnePoint alpha)) omega < ⊤ →
        ∀ t : NNReal,
          (ContinuousPath.exitTime
            (Set.range ((↑) : alpha → OnePoint alpha)) omega).toNNReal ≤ t →
            omega t = OnePoint.infty :=
  R.ae_absorbed_after_onePoint_exitTime rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    (R.kolmogorovRegular_onePointKernelSemigroup rho hrho_cont hrho_pos hrho_lipschitz
      hrho_compact htail) x

example (t : NNReal) (x : alpha) {A : Set alpha} (hA : MeasurableSet A) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint alpha) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    IsConservative.killedSemigroup R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : alpha → OnePoint alpha)) OnePoint.isOpen_range_coe
        R.isFellerKernelSemigroup_onePointKernelSemigroup
        (R.kolmogorovRegular_onePointKernelSemigroup rho hrho_cont hrho_pos hrho_lipschitz
          hrho_compact htail) t
        (PositiveC0ContractiveResolvent.onePointLiveHomeomorph x)
        (PositiveC0ContractiveResolvent.onePointLiveHomeomorph '' A) =
      R.kernelSemigroup t x A :=
  R.killedSemigroup_onePointLive_image rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    (R.kolmogorovRegular_onePointKernelSemigroup rho hrho_cont hrho_pos hrho_lipschitz
      hrho_compact htail) t x hA

example (mu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ))
    (hf0 : ∀ y, 0 ≤ f y) (x : alpha) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint alpha) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : alpha → OnePoint alpha)) OnePoint.isOpen_range_coe (mu : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          fun y ↦ ENNReal.ofReal (f y)) (x : OnePoint alpha) =
      ENNReal.ofReal (R.toContractiveResolvent.operator mu f x) :=
  R.killedResolvent_onePointLive_ofReal_eq_operator rho hrho_cont hrho_pos hrho_lipschitz
    hrho_compact (R.kolmogorovRegular_onePointKernelSemigroup rho hrho_cont hrho_pos
      hrho_lipschitz hrho_compact htail) mu f hf0 x

end OnePointRegularity

section HeatOnePointWitness

-- The heat Feller semigroup supplies an actual positive contractive resolvent. Its explicit
-- exhaustion has the ruled-in Lipschitz property. The remaining analytic tail budget is exposed
-- as an assumption, then transported through K2 and K3.
noncomputable example : PositiveC0ContractiveResolvent ℝ := heatResolvent

example :
    heatResolvent.toContractiveResolvent.generatedSemigroup =
      isFellerKernelSemigroup_heatSemigroup.c0Semigroup :=
  generatedSemigroup_heatResolvent

example (x : ℝ) : heatExhaustion x = 1 / (1 + |x|) := rfl

example : LipschitzWith 1 heatExhaustion := lipschitzWith_one_heatExhaustion

example (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    IsCompact {x : ℝ | epsilon ≤ heatExhaustion x} :=
  isCompact_heatExhaustion_superlevel epsilon hepsilon

example :
    letI := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    heatResolvent.onePointKernelSemigroup.IsConservative :=
  heatResolvent.isConservative_onePointKernelSemigroup

variable {pHeat qHeat : ℝ} {MHeat BHeat : ℝ≥0}
  {phiHeat : ℝ≥0 → ℝ → ℝ → ℝ≥0∞}
  (htailHeat : heatResolvent.onePointKernelSemigroup.HasOnePointTailBounds
    heatExhaustion continuous_heatExhaustion heatExhaustion_pos
    lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    pHeat qHeat MHeat BHeat phiHeat)

example :
    letI := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    heatResolvent.onePointKernelSemigroup.HasKolmogorovMoments
      pHeat qHeat (MHeat + BHeat) :=
  htailHeat.hasKolmogorovMoments heatResolvent.isConservative_onePointKernelSemigroup
    heatResolvent.onePointKernelSemigroup_absorbing

example :
    letI := OnePoint.exhaustionMetricSpace heatExhaustion continuous_heatExhaustion
      heatExhaustion_pos lipschitzWith_one_heatExhaustion isCompact_heatExhaustion_superlevel
    heatResolvent.onePointKernelSemigroup.KolmogorovRegular
      heatResolvent.isConservative_onePointKernelSemigroup :=
  heatResolvent.kolmogorovRegular_onePointKernelSemigroup heatExhaustion
    continuous_heatExhaustion heatExhaustion_pos lipschitzWith_one_heatExhaustion
    isCompact_heatExhaustion_superlevel htailHeat

end HeatOnePointWitness

example (theta : ℝ) (v : C₀(alpha, ℝ))
    (hcomp : ∀ mu : Semigroup.PositiveShift, theta < (mu : ℝ) → ∀ x,
      (mu : ℝ) * R.toContractiveResolvent.operator mu v x ≤
        (mu : ℝ) / ((mu : ℝ) - theta) * v x)
    (t : NNReal) (x : alpha) :
    R.toContractiveResolvent.generatedSemigroup t v x ≤
      Real.exp (theta * (t : ℝ)) * v x :=
  R.generatedSemigroup_apply_le_exp_mul theta v hcomp t x
end Resolvent

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

example (x : alpha) :
    IsConservative.continuousProcess (idSemigroup (alpha := alpha)) isConservative_idSemigroup x =
      Measure.dirac (ContinuousMap.const NNReal x) :=
  continuousProcess_idSemigroup_eq x

example (t : NNReal) (x : ℝ) :
    (brownianMotion x).map (fun omega ↦ omega t) = gaussianReal x t :=
  brownianMotion_map_eval t x

example (x : ℝ) :
    IsBrownianReal (fun (t : NNReal) (omega : ContinuousPath ℝ) ↦ omega t - x)
      (brownianMotion x) :=
  isBrownianReal_brownianMotion x

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

example (T : NNReal) {r eps : ℝ≥0∞} (hr : 0 < r) (heps : 0 < eps) :
    ∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ x : alpha,
      IsConservative.continuousProcess P hP x (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps :=
  IsConservative.exists_measure_compl_modulusSet_le P hP hmom T hr heps

section Tightness
variable [ProperSpace alpha]

example {K0 : Set alpha} (hK0 : IsCompact K0) :
    IsTightMeasureSet ((fun x ↦ IsConservative.continuousProcess P hP x) '' K0) :=
  IsConservative.isTightMeasureSet_continuousProcess P hP hmom hK0
end Tightness

section WeakContinuity
variable [ProperSpace alpha]

example (F : ContinuousPath alpha →ᵇ ℝ) :
    Continuous fun x ↦ ∫ omega, F omega ∂(IsConservative.continuousProcess P hP x) :=
  hFeller.continuous_integral_continuousProcess P hP hmom F

example : Continuous (IsConservative.pathLaw P hP) :=
  hFeller.continuous_pathLaw P hP hmom
end WeakContinuity

section Gluing
variable (R : PositiveC0ContractiveResolvent alpha)

example (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    ∫⁻ y, f y ∂P.resolventPotential lam x = P.kernelResolvent lam f x :=
  P.lintegral_resolventPotential lam hf x

example {lam mu : ℝ} (hlt : lam < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    P.kernelResolvent lam f x =
      P.kernelResolvent mu f x +
        ENNReal.ofReal (mu - lam) * P.kernelResolvent lam (P.kernelResolvent mu f) x :=
  P.kernelResolvent_resolventEquation hlt hf x

example {U V : Set alpha} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V) (lam : ℝ)
    {f g : alpha → ℝ≥0∞} (hfg : f ≤ g) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x ≤
      IsConservative.killedResolvent P hP V hV lam g x :=
  IsConservative.killedResolvent_mono P hP U hU hV hUV lam hfg x

example {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    P.kernelResolvent lam (fun _ ↦ 1) x = ENNReal.ofReal lam⁻¹ :=
  hP.kernelResolvent_one hlam x

example {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    ENNReal.ofReal lam * P.kernelResolvent lam (fun _ ↦ 1) x = 1 :=
  hP.ofReal_mul_kernelResolvent_one hlam x

example (hreg : R.OnePointRegular) (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : alpha → OnePoint alpha)) OnePoint.isOpen_range_coe lam
        (PositiveC0ContractiveResolvent.onePointLiveExtension f) (x : OnePoint alpha) =
      R.kernelSemigroup.kernelResolvent lam f x :=
  hreg.killedResolvent_live_eq_kernelResolvent lam hf x

section Family

-- The local state spaces, their resolvents, the two families of embeddings, the regularity
-- data selecting each compactified process, and the part-process identity between consecutive
-- members.
variable {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]
  (Rloc : ∀ m, PositiveC0ContractiveResolvent (X m))
  (embed : ∀ m, X m → alpha) (incl : ∀ m, X m → X (m + 1))
  (hembed : ∀ m, MeasurableEmbedding (embed m))
  (hincl : ∀ m, Topology.IsOpenEmbedding (incl m))
  (hnest : ∀ m (y : X m), embed (m + 1) (incl m y) = embed m y)
  (hregular : ∀ m, (Rloc m).OnePointRegular)
  (hpart : ∀ m, PositiveC0ContractiveResolvent.IsPartProcess (Rloc m) (Rloc (m + 1))
    (hregular (m + 1)) (hincl m))

example {lam : ℝ} (hlam : 0 < lam) (m : ℕ) {g : X (m + 1) → ℝ≥0∞} (hg : Measurable g)
    (y : X m) :
    (Rloc m).kernelSemigroup.kernelResolvent lam (fun z ↦ g (incl m z)) y ≤
      (Rloc (m + 1)).kernelSemigroup.kernelResolvent lam g (incl m y) :=
  PositiveC0ContractiveResolvent.kernelResolvent_le_of_partProcess (Rloc m) (Rloc (m + 1))
    (hregular (m + 1)) (hincl m) (hpart m) hlam hg y

example {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ≥0∞} (hf : Measurable f) (m : ℕ) (x : alpha) :
    localResolvent Rloc embed m lam f x ≤ localResolvent Rloc embed (m + 1) lam f x :=
  localResolvent_le_succ Rloc embed incl hembed hincl hnest hregular hpart hlam hf m x

example {lam : ℝ} {f : alpha → ℝ≥0∞} (x : alpha) :
    minimalResolvent Rloc embed lam f x = ⨆ m, localResolvent Rloc embed m lam f x := rfl

example {lam : ℝ} {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    Measurable (minimalResolvent Rloc embed lam f) :=
  measurable_minimalResolvent Rloc embed hembed lam hf

example {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    ENNReal.ofReal lam * minimalResolvent Rloc embed lam (fun _ ↦ 1) x ≤ 1 :=
  ofReal_mul_minimalResolvent_one_le Rloc embed (fun m ↦ (hembed m).injective) hlam x

example {lam mu : ℝ} (hlam : 0 < lam) (hlt : lam < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    minimalResolvent Rloc embed lam f x =
      minimalResolvent Rloc embed mu f x +
        ENNReal.ofReal (mu - lam) *
          minimalResolvent Rloc embed lam (minimalResolvent Rloc embed mu f) x :=
  minimalResolvent_resolventEquation Rloc embed incl hembed hincl hnest hregular hpart hlam hlt
    hf x

-- The part-process identity is consumed only through the monotonicity of the transported
-- resolvents in the index.
example : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
    Monotone fun m ↦ localResolvent Rloc embed m nu h y :=
  fun _nu hnu {_h} hh y ↦
    monotone_localResolvent Rloc embed incl hembed hincl hnest hregular hpart hnu hh y

variable (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
    Monotone fun m ↦ localResolvent Rloc embed m nu h y)

example {lam mu : ℝ} (hlam : 0 < lam) (hlt : lam < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    minimalResolvent Rloc embed lam f x =
      minimalResolvent Rloc embed mu f x +
        ENNReal.ofReal (mu - lam) *
          minimalResolvent Rloc embed lam (minimalResolvent Rloc embed mu f) x :=
  minimalResolvent_resolventEquation_of_monotone Rloc embed hembed hmono hlam hlt hf x

example {lam : ℝ} (hlam : 0 < lam) {f g : alpha → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (x : alpha) :
    minimalResolvent Rloc embed lam (fun y ↦ f y + g y) x =
      minimalResolvent Rloc embed lam f x + minimalResolvent Rloc embed lam g x :=
  minimalResolvent_add Rloc embed hembed hmono hlam hf hg x

example (lam : ℝ) (c : ℝ≥0∞) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    minimalResolvent Rloc embed lam (fun y ↦ c * f y) x =
      c * minimalResolvent Rloc embed lam f x :=
  minimalResolvent_const_mul Rloc embed hembed lam c hf x

example {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ≥0∞} {c : ℝ≥0∞} (hfc : ∀ y, f y ≤ c)
    (x : alpha) :
    minimalResolvent Rloc embed lam f x ≤ c * ENNReal.ofReal lam⁻¹ :=
  minimalResolvent_le_of_le_const Rloc embed hembed hlam hfc x

example {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    minimalResolvent Rloc embed lam (minimalResolvent Rloc embed mu f) x =
      minimalResolvent Rloc embed mu (minimalResolvent Rloc embed lam f) x :=
  minimalResolvent_comm Rloc embed hembed hmono hlam hmu hf x

example {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    |minimalResolventReal Rloc embed lam f x| ≤ D / lam :=
  abs_minimalResolventReal_le Rloc embed hembed hlam hfD x

example {lam : ℝ} {f : alpha → ℝ} (hf : Measurable f) :
    Measurable (minimalResolventReal Rloc embed lam f) :=
  measurable_minimalResolventReal Rloc embed hembed lam hf

example {lam : ℝ} (hlam : 0 < lam) {f g : alpha → ℝ} {D E : ℝ} (hf : Measurable f)
    (hg : Measurable g) (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E) (x : alpha) :
    minimalResolventReal Rloc embed lam (fun y ↦ f y + g y) x =
      minimalResolventReal Rloc embed lam f x + minimalResolventReal Rloc embed lam g x :=
  minimalResolventReal_add Rloc embed hembed hmono hlam hf hg hfD hgE x

example {lam mu : ℝ} (hlam : 0 < lam) (hlt : lam < mu) {f : alpha → ℝ} {D : ℝ}
    (hf : Measurable f) (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    minimalResolventReal Rloc embed lam f x =
      minimalResolventReal Rloc embed mu f x +
        (mu - lam) * minimalResolventReal Rloc embed lam
          (fun z ↦ minimalResolventReal Rloc embed mu f z) x :=
  minimalResolventReal_resolventEquation Rloc embed hembed hmono hlam hlt hf hfD x

example {lam : ℝ} (hlam : 0 < lam) (x : alpha) {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂minimalPotential Rloc embed hembed hmono hlam x =
      minimalResolvent Rloc embed lam f x :=
  lintegral_minimalPotential Rloc embed hembed hmono hlam x hf

-- The two analytic inputs on `C₀`: the values of the supremum resolvent are again continuous and
-- vanish at infinity, and their range is dense.
variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))
  (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
    T nu f x = minimalResolventReal Rloc embed (nu : ℝ) (fun y ↦ f y) x)
  (hdense : ∀ nu, DenseRange (T nu))

noncomputable example : PositiveC0ContractiveResolvent alpha :=
  minimalC0Resolvent Rloc embed T hembed hmono hT hdense

example {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    (minimalC0Resolvent Rloc embed T hembed hmono hT hdense).kernelSemigroup.kernelResolvent
        lam f x =
      minimalResolvent Rloc embed lam f x :=
  kernelResolvent_minimalC0Resolvent Rloc embed T hembed hmono hT hdense hlam hf x

example {lam : ℝ} (hlam : 0 < lam)
    (hone : ∀ x, ENNReal.ofReal lam * minimalResolvent Rloc embed lam (fun _ ↦ 1) x = 1) :
    (minimalC0Resolvent Rloc embed T hembed hmono hT hdense).kernelSemigroup.IsConservative :=
  isConservative_kernelSemigroup_minimalC0Resolvent Rloc embed T hembed hmono hT hdense hlam hone

example (hreg : (minimalC0Resolvent Rloc embed T hembed hmono hT hdense).OnePointRegular)
    {lam : ℝ} (hlam : 0 < lam)
    (hone : ∀ x, ENNReal.ofReal lam * minimalResolvent Rloc embed lam (fun _ ↦ 1) x = 1)
    (x : alpha) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    ∀ᵐ omega ∂IsConservative.continuousProcess
        (minimalC0Resolvent Rloc embed T hembed hmono hT hdense).onePointKernelSemigroup
        (minimalC0Resolvent Rloc embed T hembed hmono hT
          hdense).isConservative_onePointKernelSemigroup (x : OnePoint alpha),
      ContinuousPath.exitTime (Set.range ((↑) : alpha → OnePoint alpha)) omega = ⊤ :=
  ae_exitTime_eq_top_minimalC0Resolvent Rloc embed T hembed hmono hT hdense hreg hlam hone x

end Family

-- The constant family: every local space is the whole space and every embedding is the identity,
-- so the supremum resolvent is the kernel resolvent itself.
example (S : PositiveC0ContractiveResolvent alpha) (lam : ℝ) (f : alpha → ℝ≥0∞) (x : alpha) :
    minimalResolvent (fun _ : ℕ ↦ S) (fun _ : ℕ ↦ (id : alpha → alpha)) lam f x =
      S.kernelSemigroup.kernelResolvent lam f x := by
  have hlocal : ∀ m : ℕ,
      localResolvent (fun _ : ℕ ↦ S) (fun _ : ℕ ↦ (id : alpha → alpha)) m lam f x =
        S.kernelSemigroup.kernelResolvent lam f x := fun m ↦
    localResolvent_apply (fun _ : ℕ ↦ S) (fun _ : ℕ ↦ (id : alpha → alpha))
      Function.injective_id lam f x
  simp only [minimalResolvent, hlocal, ciSup_const]

-- The regularity data of a compactified process are available for the heat semigroup.
noncomputable example : heatResolvent.OnePointRegular := onePointRegular_heatResolvent

example (x : ℝ) :
    letI := onePointRegular_heatResolvent.metricSpace
    letI := onePointRegular_heatResolvent.completeSpace
    ∀ᵐ omega ∂IsConservative.continuousProcess heatResolvent.onePointKernelSemigroup
        heatResolvent.isConservative_onePointKernelSemigroup (x : OnePoint ℝ),
      ContinuousPath.exitTime (Set.range ((↑) : ℝ → OnePoint ℝ)) omega = ⊤ :=
  ae_exitTime_eq_top_heatResolvent x

end Gluing
