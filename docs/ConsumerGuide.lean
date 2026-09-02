/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
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

/-!
# Consumer guide probe

The code blocks of `docs/CONSUMER_GUIDE.md`, verbatim, so that the guide is checked against the
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

example (Q : Kernel alpha (ContinuousPath alpha)) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) :
    Q = IsConservative.continuousProcess P hP :=
  IsConservative.eq_continuousProcess_of_map_finiteEvaluation P hP
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) Q hQ

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

example (μ : Semigroup.PositiveShift) :
    R.isFellerKernelSemigroup_kernelSemigroup.c0Semigroup.resolvent μ =
      R.toContractiveResolvent.operator μ :=
  R.resolvent_c0Semigroup_kernelSemigroup μ
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
