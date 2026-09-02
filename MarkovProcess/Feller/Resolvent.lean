/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import MarkovProcess.Feller.Semigroup
import MarkovProcess.Kernel.PositiveC0Resolvent
import MarkovProcess.Semigroup.Resolvent
import MarkovProcess.Semigroup.ResolventGeneration

/-!
# The resolvent of a Feller kernel semigroup

The resolvent of the `C₀` semigroup of a Feller kernel semigroup `P`, evaluated at a point, is
the Laplace transform of the transition integrals,

  `R_μ f (x) = ∫₀^∞ e^{-μ t} (∫ f d(P t x)) dt`   (`IsFellerKernelSemigroup.resolvent_apply_apply`),

and the generator domain of the `C₀` semigroup is the range of this resolvent
(`IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent`), the kernel-side reading of
`Semigroup/Resolvent.lean`.  Evaluation at a point is packaged as the bounded functional
`c0EvalCLM`, which commutes with Bochner integrals in `C₀(α, ℝ)`.  For the Feller kernel
semigroup represented by a positive contractive resolvent `R` (`Kernel/PositiveC0Resolvent.lean`),
the resolvent of its `C₀` semigroup is `R` itself
(`PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup`).

Main results: `c0EvalCLM`, `IsFellerKernelSemigroup.resolvent_apply_apply`,
`IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent`,
`PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup`.

Nothing is asserted about the resolvent as a kernel: the Laplace transform is taken of the `C₀`
operators, not of the measures.
-/

open MeasureTheory Set
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

section Eval

variable {α : Type*} [TopologicalSpace α]

/-- Evaluation at a point, as a bounded linear functional on `C₀(α, ℝ)`. -/
noncomputable def c0EvalCLM (x : α) : C₀(α, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ f x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl } 1 fun f ↦ by
    rw [one_mul, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF x

/-- Evaluation, unfolded. -/
@[simp]
theorem c0EvalCLM_apply (x : α) (f : C₀(α, ℝ)) : c0EvalCLM x f = f x :=
  rfl

end Eval

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [LocallyCompactSpace α] [T2Space α]
variable {P : SubMarkovKernelSemigroup α} (hP : P.IsFellerKernelSemigroup)

/-- **The resolvent of the `C₀` semigroup, evaluated at a point**: the Laplace transform of the
transition integrals. -/
theorem IsFellerKernelSemigroup.resolvent_apply_apply (μ : Semigroup.PositiveShift)
    (f : C₀(α, ℝ)) (x : α) :
    hP.c0Semigroup.resolvent μ f x =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(μ : ℝ) * t) * kernelIntegral (P (Real.toNNReal t)) f x := by
  rw [← c0EvalCLM_apply x (hP.c0Semigroup.resolvent μ f),
    Semigroup.StronglyContinuousContractionSemigroup.resolvent_apply,
    ← ContinuousLinearMap.integral_comp_comm _
      (hP.c0Semigroup.integrableOn_laplaceIntegrand μ.2 f)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp only [Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, map_smul,
    c0EvalCLM_apply, smul_eq_mul, IsFellerKernelSemigroup.c0Semigroup_apply_apply]

/-- **The generator domain of the `C₀` semigroup is the range of its resolvent**, at every
positive shift. -/
theorem IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent
    (μ : Semigroup.PositiveShift) (f : C₀(α, ℝ)) :
    f ∈ hP.c0Semigroup.generatorDomain ↔ ∃ g, hP.c0Semigroup.resolvent μ g = f := by
  rw [← SetLike.mem_coe, hP.c0Semigroup.generatorDomain_eq_range_resolvent μ]
  exact Set.mem_range

end SubMarkovKernelSemigroup

namespace PositiveC0ContractiveResolvent

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (R : PositiveC0ContractiveResolvent X)

/-- **The resolvent of the represented process is the given resolvent.** -/
theorem resolvent_c0Semigroup_kernelSemigroup (μ : Semigroup.PositiveShift) :
    R.isFellerKernelSemigroup_kernelSemigroup.c0Semigroup.resolvent μ =
      R.toContractiveResolvent.operator μ := by
  rw [R.c0Semigroup_kernelSemigroup, Semigroup.ContractiveResolvent.resolvent_generatedSemigroup]

end PositiveC0ContractiveResolvent

end MarkovProcess
