import Mathlib

/-!
# Continuous Markov process — solution vocabulary (verbatim copy of the challenge)

This is a Mathlib-only comparator challenge for the main theorem of the `MarkovProcess`
library: existence and uniqueness of the continuous-path Markov process with a prescribed
conservative Feller transition semigroup on a locally compact Polish state space.

The mathematical content is the following.  Let `α` be a complete separable metric space that
is locally compact and nonempty, with its Borel sigma-algebra.  A sub-Markov kernel semigroup
`P` on `α` is a jointly measurable family of transition kernels `P t`, `t ≥ 0`, with `P 0` the
identity kernel, the Chapman–Kolmogorov law `P (s + t) = P t ∘ P s`, and every `P t x` of mass
at most one.  Assume `P` is conservative (every `P t x` is a probability measure), Feller
(integration against `P t` maps `C₀(α, ℝ)` into itself, and the resulting contraction operators
on `C₀(α, ℝ)` have norm-continuous time orbits), and satisfies a Kolmogorov moment criterion:
for some `p > 0`, `q > 1`, `M ≥ 0`, the `p`-th moment of the displacement over time `h` is at
most `M h ^ q` uniformly in the starting point.  Then there is exactly one Markov kernel `Q`
from `α` to the space `C([0, ∞), α)` of continuous paths, with the Borel sigma-algebra of the
compact-open topology, whose finite-dimensional distributions are those of `P`: for every
finite set `I` of times, the law of the coordinates at the times of `I` under `Q x` is the
iterated composition of the transitions of `P` along the increasing enumeration of `I`,
started at `x`.

Only definitions needed to read that assertion occur below.  The definitional vocabulary is a
statement-level copy of the library's (`MarkovProcess/Kernel/Basic.lean`,
`Kernel/KernelSemigroup.lean`, `Kernel/Integral.lean`, `Kernel/C0.lean`, `Feller/Semigroup.lean`,
`Time/FiniteOrderedTimes.lean`, `FiniteTime/Kernel.lean`, `FiniteTime/ProjectiveFamily.lean`,
`Path/Basic.lean`, `Kernel/KolmogorovMoments.lean`).

## Presentation deltas relative to the library

1. **Path-regularity hypothesis.** The challenge assumes the intrinsic moment bound
   `HasKolmogorovMoments` on `P`, exactly as the library's
   `existsUnique_continuousProcess_of_hasKolmogorovMoments` does; the library's other form takes
   the construction-level regularity hypothesis instead, which the moment bound implies.
2. **Sigma-algebra on path space.** The library declares the Borel sigma-algebra of the
   compact-open topology on `C(NNReal, α)`; the challenge declares the same instance.
3. **The Markov clause.** `IsMarkovKernel Q` inside the unique-existence predicate is implied by
   the empty-set marginal; it is kept for readability.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ZeroAtInfty ProbabilityTheory

namespace MarkovProcessChallenge

/-! ## 1. Sub-Markov kernels and kernel semigroups -/

section Kernels

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A kernel is sub-Markov when every fibre has mass at most one. -/
def IsSubMarkovKernel (κ : Kernel α β) : Prop :=
  ∀ x, κ x Set.univ ≤ 1

/-- A jointly measurable sub-Markov transition semigroup indexed by nonnegative time. -/
structure SubMarkovKernelSemigroup (α : Type*) [MeasurableSpace α] where
  /-- The transition kernel at a nonnegative time. -/
  kernel : NNReal → Kernel α α
  /-- Joint measurability in time and starting point. -/
  measurable_kernel : Measurable fun p : NNReal × α ↦ kernel p.1 p.2
  /-- At time zero the transition kernel is the identity kernel. -/
  kernel_zero : kernel 0 = Kernel.id
  /-- The Chapman--Kolmogorov law, in Mathlib's kernel-composition orientation. -/
  kernel_add : ∀ s t, kernel (s + t) = (kernel t).comp (kernel s)
  /-- Every transition measure has mass at most one. -/
  isSubMarkovKernel : ∀ t, IsSubMarkovKernel (kernel t)

end Kernels

namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]

instance : CoeFun (SubMarkovKernelSemigroup α) (fun _ ↦ NNReal → Kernel α α) where
  coe P := P.kernel

/-- Conservativity: every transition measure is a probability measure. -/
def IsConservative (P : SubMarkovKernelSemigroup α) : Prop :=
  ∀ t x, P t x Set.univ = 1

/-- Every transition kernel of a sub-Markov kernel semigroup is a finite kernel. -/
theorem isFiniteKernel (P : SubMarkovKernelSemigroup α) (t : NNReal) : IsFiniteKernel (P t) :=
  ⟨⟨1, ENNReal.one_lt_top, fun x ↦ P.isSubMarkovKernel t x⟩⟩

end SubMarkovKernelSemigroup

/-- The raw real-valued integral of `f` against the measure `κ x`. -/
noncomputable def kernelIntegral {α : Type*} [MeasurableSpace α] (κ : Kernel α α) (f : α → ℝ)
    (x : α) : ℝ :=
  ∫ y, f y ∂κ x

/-! ## 2. The `C₀` action and the Feller property -/

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]

/-- A kernel semigroup maps `C₀(α, ℝ)` into itself when its raw kernel integral is continuous
and vanishes at infinity at every time. -/
def MapsC0 (P : SubMarkovKernelSemigroup α) : Prop :=
  ∀ t (f : C₀(α, ℝ)),
    Continuous (kernelIntegral (P t) f) ∧
      Tendsto (kernelIntegral (P t) f) (cocompact α) (nhds 0)

variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)

/-- The exact `C₀` representative obtained by integrating against `P t`. -/
noncomputable def c0KernelIntegral (t : NNReal) (f : C₀(α, ℝ)) : C₀(α, ℝ) where
  toFun := kernelIntegral (P t) f
  continuous_toFun := (hC0 t f).1
  zero_at_infty' := (hC0 t f).2

variable [BorelSpace α]

/-- Every `C₀` function is integrable against each transition measure. -/
theorem integrable_fiber (t : NNReal) (f : C₀(α, ℝ)) (x : α) :
    Integrable f (P t x) := by
  letI : IsFiniteKernel (P t) := P.isFiniteKernel t
  exact f.toBCF.integrable (P t x)

/-- The `C₀` kernel integral is a contraction. -/
theorem norm_c0KernelIntegral_le (t : NNReal) (f : C₀(α, ℝ)) :
    ‖P.c0KernelIntegral hC0 t f‖ ≤ ‖f‖ := by
  letI : IsFiniteKernel (P t) := P.isFiniteKernel t
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).2
  intro x
  calc
    ‖P.c0KernelIntegral hC0 t f x‖
        ≤ (P t x).real Set.univ * ‖f.toBCF‖ :=
      f.toBCF.norm_integral_le_mul_norm (P t x)
    _ ≤ 1 * ‖f.toBCF‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [Measure.real_def]
      exact ENNReal.toReal_mono ENNReal.one_ne_top (P.isSubMarkovKernel t x)
    _ = ‖f‖ := by
      rw [one_mul, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]

/-- The kernel integral as a contraction on real continuous functions vanishing at infinity. -/
noncomputable def c0Operator (t : NNReal) : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ) :=
  LinearMap.mkContinuous
    { toFun := P.c0KernelIntegral hC0 t
      map_add' := fun f g ↦ by
        apply ZeroAtInftyContinuousMap.ext
        intro x
        change ∫ y, (f y + g y) ∂P t x = (∫ y, f y ∂P t x) + ∫ y, g y ∂P t x
        exact integral_add (P.integrable_fiber t f x) (P.integrable_fiber t g x)
      map_smul' := fun c f ↦ by
        apply ZeroAtInftyContinuousMap.ext
        intro x
        change ∫ y, c * f y ∂P t x = c * ∫ y, f y ∂P t x
        simpa only [smul_eq_mul] using
          (integral_smul c (fun y ↦ f y) :
            (∫ y, c • f y ∂P t x) = c • ∫ y, f y ∂P t x) }
    1 fun f ↦ by
      rw [one_mul]
      exact P.norm_c0KernelIntegral_le hC0 t f

/-- The `C₀` kernel operators have continuous time orbits in the `C₀` norm. -/
def HasContinuousC0Orbits : Prop :=
  ∀ f : C₀(α, ℝ), Continuous fun t : NNReal ↦ P.c0Operator hC0 t f

/-- The Feller property: `P` maps `C₀` into itself with norm-continuous time orbits. -/
def IsFellerKernelSemigroup [LocallyCompactSpace α] [T2Space α] : Prop :=
  ∃ hC0 : P.MapsC0, P.HasContinuousC0Orbits hC0

end SubMarkovKernelSemigroup

/-! ## 3. Finite-dimensional distributions -/

/-- A strictly increasing family of `n` nonnegative times. -/
abbrev FiniteOrderedTimes (n : ℕ) := Fin n ↪o NNReal

namespace FiniteOrderedTimes

/-- The times after the first one, shifted so that the first time becomes zero. -/
def relativeTail {n : ℕ} (times : FiniteOrderedTimes (n + 1)) : FiniteOrderedTimes n :=
  OrderEmbedding.ofStrictMono (fun i ↦ times i.succ - times 0) fun _ _ hij ↦
    tsub_lt_tsub_right_of_le (times.monotone (Fin.zero_le _))
      (times.strictMono (Fin.strictMono_succ hij))

/-- The unique path indexed by the empty finite type. -/
def emptyPath (α : Type*) : Fin 0 → α :=
  Fin.elim0

end FiniteOrderedTimes

namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]

/-- Prepending a coordinate to a finite path is measurable. -/
theorem measurable_finCons {n : ℕ} :
    Measurable (fun z : α × (Fin n → α) ↦
      @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : α × (Fin n → α) → α))
  · simpa only [Fin.cons_succ] using
      (measurable_pi_apply j).comp (measurable_snd : Measurable (Prod.snd : α × (Fin n → α) → _))

/-- The finite-time kernel obtained by recursively sampling a strictly ordered family of times:
sample at the first time, then iterate along the increments. -/
noncomputable def finiteTimeKernel (P : SubMarkovKernelSemigroup α) :
    {n : ℕ} → FiniteOrderedTimes n → Kernel α (Fin n → α)
  | 0, _ => Kernel.const α (Measure.dirac (FiniteOrderedTimes.emptyPath α))
  | n + 1, times =>
      Kernel.mapOfMeasurable
        (P (times 0) ⊗ₖ Kernel.prodMkLeft α (finiteTimeKernel P times.relativeTail))
        (fun z ↦ @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2) measurable_finCons

/-- The increasing enumeration of a finite set of nonnegative times. -/
noncomputable def finiteSetTimes (I : Finset NNReal) : FiniteOrderedTimes I.card :=
  I.orderEmbOfFin rfl

/-- Reindex an ordered coordinate path by its finite set of times. -/
noncomputable def orderedPathToFiniteSet (I : Finset NNReal) (path : Fin I.card → α) : I → α :=
  fun t ↦ path ((I.orderIsoOfFin rfl).symm t)

/-- Reindexing an ordered coordinate path by its finite set of times is measurable. -/
theorem measurable_orderedPathToFiniteSet (I : Finset NNReal) :
    Measurable (orderedPathToFiniteSet (α := α) I) :=
  measurable_pi_iff.mpr fun t ↦ measurable_pi_apply ((I.orderIsoOfFin rfl).symm t)

/-- The finite-dimensional distribution of `P` at the times of `I`, indexed by `I`. -/
noncomputable def finiteSetKernel (P : SubMarkovKernelSemigroup α) (I : Finset NNReal) :
    Kernel α (I → α) :=
  Kernel.mapOfMeasurable (finiteTimeKernel P (finiteSetTimes I))
    (orderedPathToFiniteSet I) (measurable_orderedPathToFiniteSet I)

/-! ## 4. The Kolmogorov moment criterion -/

variable [TopologicalSpace α]

/-- A uniform `p`-th moment bound of order `h ^ q` on the displacement of `P` over time `h`. -/
def HasKolmogorovMoments [PseudoEMetricSpace α] (P : SubMarkovKernelSemigroup α) (p q : ℝ)
    (M : ℝ≥0) : Prop :=
  0 < p ∧ 1 < q ∧ ∀ (h : NNReal) (y : α), ∫⁻ z, edist z y ^ p ∂(P h y) ≤ M * (h : ℝ≥0∞) ^ q

end SubMarkovKernelSemigroup

/-! ## 5. Continuous paths -/

/-- Continuous paths on nonnegative real time, with the compact-open topology. -/
abbrev ContinuousPath (α : Type*) [TopologicalSpace α] := C(NNReal, α)

namespace ContinuousPath

variable {α : Type*} [TopologicalSpace α]

/-- The Borel sigma-algebra of the compact-open topology on continuous paths. -/
scoped instance measurableSpace : MeasurableSpace (ContinuousPath α) := borel _

/-- Evaluation of a path at the times of a finite set, indexed by that set. -/
def finsetEvaluation (I : Finset NNReal) : ContinuousPath α → (I → α) :=
  fun path t ↦ path (t : NNReal)

end ContinuousPath

end MarkovProcessChallenge
