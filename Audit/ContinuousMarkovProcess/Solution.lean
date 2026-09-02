import MarkovProcess.Main
import Audit.ContinuousMarkovProcess.SolutionBasic

/-!
# Continuous Markov process — comparator solution

Proves the challenge theorem `MarkovProcessChallenge.existsUnique_continuousMarkovProcess` from
the library.  The challenge's vocabulary (`SolutionBasic.lean`, a verbatim Mathlib-only copy of
the challenge) is bridged to the library's definitions by the private lemmas below; every
bridge is definitional or a structural induction, and the theorem itself is the library's
`IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments` transported
along those bridges.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ZeroAtInfty ProbabilityTheory

namespace MarkovProcessChallenge

section Bridges

variable {α : Type*} [MeasurableSpace α]

/-- The challenge's kernel semigroup as a library kernel semigroup (identical fields). -/
private def toLib (P : SubMarkovKernelSemigroup α) : MarkovProcess.SubMarkovKernelSemigroup α where
  kernel := P.kernel
  measurable_kernel := P.measurable_kernel
  kernel_zero := P.kernel_zero
  kernel_add := P.kernel_add
  isSubMarkovKernel := P.isSubMarkovKernel

private theorem toLib_apply (P : SubMarkovKernelSemigroup α) (t : NNReal) :
    toLib P t = P t := rfl

private theorem isConservative_toLib {P : SubMarkovKernelSemigroup α} (hP : P.IsConservative) :
    (toLib P).IsConservative := hP

/-- The two recursively defined finite-time kernels agree. -/
private theorem finiteTimeKernel_eq (P : SubMarkovKernelSemigroup α) :
    ∀ {n : ℕ} (times : FiniteOrderedTimes n),
      SubMarkovKernelSemigroup.finiteTimeKernel P times =
        MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel (toLib P) times
  | 0, _ => rfl
  | n + 1, times => by
      show Kernel.mapOfMeasurable
          (P (times 0) ⊗ₖ Kernel.prodMkLeft α
            (SubMarkovKernelSemigroup.finiteTimeKernel P times.relativeTail)) _ _ = _
      rw [finiteTimeKernel_eq P times.relativeTail]
      rfl

private theorem finiteSetKernel_eq (P : SubMarkovKernelSemigroup α) (I : Finset NNReal) :
    SubMarkovKernelSemigroup.finiteSetKernel P I =
      MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel (toLib P) I := by
  unfold SubMarkovKernelSemigroup.finiteSetKernel MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
  rw [finiteTimeKernel_eq]
  rfl

variable [TopologicalSpace α]

private theorem mapsC0_toLib {P : SubMarkovKernelSemigroup α} (h : P.MapsC0) :
    (toLib P).MapsC0 := h

private theorem isFellerKernelSemigroup_toLib [BorelSpace α] [LocallyCompactSpace α] [T2Space α]
    {P : SubMarkovKernelSemigroup α} (h : P.IsFellerKernelSemigroup) :
    (toLib P).IsFellerKernelSemigroup := by
  obtain ⟨hC0, hOrbit⟩ := h
  exact ⟨mapsC0_toLib hC0, fun f ↦ hOrbit f⟩

omit [TopologicalSpace α] in
private theorem hasKolmogorovMoments_toLib [PseudoEMetricSpace α]
    {P : SubMarkovKernelSemigroup α} {p q : ℝ} {M : ℝ≥0}
    (h : P.HasKolmogorovMoments p q M) : (toLib P).HasKolmogorovMoments p q M := h

omit [MeasurableSpace α] in
private theorem finsetEvaluation_eq (I : Finset NNReal) :
    (ContinuousPath.finsetEvaluation (α := α) I) =
      MarkovProcess.ContinuousPath.finsetEvaluation (alpha := α) I := rfl

end Bridges

open ContinuousPath in
/-- **Existence and uniqueness of the continuous Markov process.**  For a conservative Feller
sub-Markov kernel semigroup satisfying the Kolmogorov moment criterion on a locally compact
Polish state space, there is exactly one Markov kernel from the state space to continuous
paths whose finite-dimensional distributions at every finite set of times are the iterated
transition laws of the semigroup. -/
theorem existsUnique_continuousMarkovProcess
    {α : Type*} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [LocallyCompactSpace α] [Nonempty α] [MeasurableSpace α] [BorelSpace α]
    (P : SubMarkovKernelSemigroup α) (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) :
    ∃! Q : Kernel α (ContinuousPath α), IsMarkovKernel Q ∧
      ∀ I : Finset NNReal, Q.map (ContinuousPath.finsetEvaluation I) = P.finiteSetKernel I := by
  have h := MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.existsUnique_continuousProcess_of_hasKolmogorovMoments
    (toLib P) (isConservative_toLib hP) (isFellerKernelSemigroup_toLib hFeller)
    (hasKolmogorovMoments_toLib hmom)
  simpa only [finiteSetKernel_eq, finsetEvaluation_eq] using h

end MarkovProcessChallenge
