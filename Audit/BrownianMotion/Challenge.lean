import Mathlib

/-!
# Brownian motion — comparator challenge

A Mathlib-only comparator challenge for the identification of one-dimensional Brownian motion
as the continuous-path Markov process of the heat semigroup, together with the identification of
its generator as half the Laplacian.

The mathematical content is the following.  The heat kernels `P t x = N(x, t)`, the Gaussian
laws with mean `x` and variance `t`, form the transition semigroup of Brownian motion.

1. **Existence and uniqueness.**  There is exactly one Markov kernel `Q` from `ℝ` to the space
   `C([0, ∞), ℝ)` of continuous paths, with the Borel sigma-algebra of the compact-open
   topology, whose finite-dimensional distributions are those of the heat kernels: for every
   finite set `I` of times, the law of the coordinates at the times of `I` under `Q x` is the
   iterated composition of the heat kernels along the increasing enumeration of `I`, started
   at `x`.
2. **Brownian motion.**  Under every such `Q x`, the centred canonical process
   `ω ↦ ω t − x` is a Brownian motion: each `ω t − x` has law `N(0, t)`, the increments over
   any increasing family of times are independent, and paths are continuous.  Mathlib defines
   `IsBrownianReal` by the Gaussian finite-dimensional laws and continuous paths and proves it
   equivalent to these three conditions (`HasIndepIncrements.isPreBrownianReal_of_hasLaw` and
   the converse lemmas `IsPreBrownianReal.hasLaw_eval`, `IsPreBrownianReal.hasIndepIncrements`);
   the pinned revision predates them, so `HasIndepIncrements` below is Mathlib's definition
   copied verbatim and `IsBrownianReal` below is the equivalent form.
3. **The generator.**  For every twice continuously differentiable `f : ℝ → ℝ` with `f` and
   `f''` vanishing at infinity, `t⁻¹ (P_t f − f) → ½ f''` uniformly on `ℝ` as `t → 0⁺`:
   the generator of the heat semigroup on `C₀(ℝ)` is half the Laplacian on such functions.

Only definitions needed to read that assertion occur below; the finite-dimensional vocabulary
is the same as in `Audit/ContinuousMarkovProcess/Challenge.lean`, specialized to the heat
kernels.

## Presentation deltas relative to the library

1. The second conjunct quantifies over every Markov kernel with the heat-kernel
   finite-dimensional distributions instead of naming the library's `brownianMotion`, which is
   the unique such kernel by the first conjunct.
2. The third conjunct is the uniform limit of the explicit Gaussian difference quotients
   (`tendstoUniformly_gaussianAverage_sub_div`); the library also states it on the generator of
   the `C₀` semigroup of the heat semigroup (`generator_heatSemigroup`), an object the challenge
   does not define.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace BrownianMotionChallenge

/-! ## 1. The heat kernels -/

/-- Translating a Gaussian law is measurable in the translation: the measurability of
`x ↦ N(x, t)`. -/
theorem measurable_gaussianReal_left (t : NNReal) :
    Measurable fun x : ℝ ↦ gaussianReal x t := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  have h : ∀ x : ℝ, gaussianReal x t s = gaussianReal 0 t (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ∈ s}) := by
    intro x
    have hmap : (gaussianReal 0 t).map (fun y ↦ y + x) = gaussianReal x t := by
      rw [gaussianReal_map_add_const, zero_add]
    rw [← hmap, Measure.map_apply (measurable_add_const x) hs]
    congr 1
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, add_comm]
  simp_rw [h]
  exact measurable_measure_prodMk_left
    ((measurable_fst.add measurable_snd) hs)

/-- The heat kernel at time `t`: the Gaussian law with mean the starting point and variance
`t`. -/
noncomputable def heatKernel (t : NNReal) : Kernel ℝ ℝ :=
  ⟨fun x ↦ gaussianReal x t, measurable_gaussianReal_left t⟩

/-! ## 2. Finite-dimensional distributions -/

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

/-- Prepending a coordinate to a finite path is measurable. -/
theorem measurable_finCons {α : Type*} [MeasurableSpace α] {n : ℕ} :
    Measurable (fun z : α × (Fin n → α) ↦
      @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : α × (Fin n → α) → α))
  · simpa only [Fin.cons_succ] using
      (measurable_pi_apply j).comp (measurable_snd : Measurable (Prod.snd : α × (Fin n → α) → _))

/-- The finite-time law of the heat kernels along a strictly ordered family of times: sample at
the first time, then iterate along the increments. -/
noncomputable def heatFiniteTimeKernel :
    {n : ℕ} → FiniteOrderedTimes n → Kernel ℝ (Fin n → ℝ)
  | 0, _ => Kernel.const ℝ (Measure.dirac (FiniteOrderedTimes.emptyPath ℝ))
  | n + 1, times =>
      Kernel.mapOfMeasurable
        (heatKernel (times 0) ⊗ₖ Kernel.prodMkLeft ℝ (heatFiniteTimeKernel times.relativeTail))
        (fun z ↦ @Fin.cons n (fun _ : Fin (n + 1) ↦ ℝ) z.1 z.2) measurable_finCons

/-- The increasing enumeration of a finite set of nonnegative times. -/
noncomputable def finiteSetTimes (I : Finset NNReal) : FiniteOrderedTimes I.card :=
  I.orderEmbOfFin rfl

/-- Reindex an ordered coordinate path by its finite set of times. -/
noncomputable def orderedPathToFiniteSet (I : Finset NNReal) (path : Fin I.card → ℝ) : I → ℝ :=
  fun t ↦ path ((I.orderIsoOfFin rfl).symm t)

/-- Reindexing an ordered coordinate path by its finite set of times is measurable. -/
theorem measurable_orderedPathToFiniteSet (I : Finset NNReal) :
    Measurable (orderedPathToFiniteSet I) :=
  measurable_pi_iff.mpr fun t ↦ measurable_pi_apply ((I.orderIsoOfFin rfl).symm t)

/-- The finite-dimensional distribution of the heat kernels at the times of `I`, indexed by
`I`. -/
noncomputable def heatFiniteSetKernel (I : Finset NNReal) : Kernel ℝ (I → ℝ) :=
  Kernel.mapOfMeasurable (heatFiniteTimeKernel (finiteSetTimes I))
    (orderedPathToFiniteSet I) (measurable_orderedPathToFiniteSet I)

/-! ## 3. Continuous paths -/

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

/-! ## 4. Brownian motion -/

/-- A process has independent increments when, for every increasing family of times
`t 0 ≤ t 1 ≤ ⋯ ≤ t n`, the increments `X (t 1) − X (t 0), …, X (t n) − X (t (n-1))` are
independent.  This is the definition of `ProbabilityTheory.HasIndepIncrements` in Mathlib. -/
def HasIndepIncrements {T Ω E : Type*} [Preorder T] [MeasurableSpace Ω] [MeasurableSpace E]
    [Sub E] (X : T → Ω → E) (P : Measure Ω) : Prop :=
  ∀ n, ∀ t : Fin (n + 1) → T, Monotone t →
    iIndepFun (fun (i : Fin n) ω ↦ X (t i.succ) ω - X (t i.castSucc) ω) P

/-- A real process indexed by nonnegative time is a **Brownian motion** when each `X t` has
the Gaussian law of mean `0` and variance `t`, the increments are independent, and almost
every path is continuous.  Mathlib's `HasIndepIncrements.isPreBrownianReal_of_hasLaw`, with
the converse lemmas `IsPreBrownianReal.hasLaw_eval` and `IsPreBrownianReal.hasIndepIncrements`,
proves the first two conditions equivalent to the finite-dimensional laws being those of
Brownian motion, so this structure is equivalent to Mathlib's `IsBrownianReal`. -/
structure IsBrownianReal {Ω : Type*} [MeasurableSpace Ω] (X : NNReal → Ω → ℝ) (P : Measure Ω) :
    Prop where
  /-- Each coordinate has the centred Gaussian law with variance the time. -/
  hasLaw_eval : ∀ t, HasLaw (X t) (gaussianReal 0 t) P
  /-- The increments over increasing times are independent. -/
  hasIndepIncrements : HasIndepIncrements X P
  /-- Almost every path is continuous. -/
  cont : ∀ᵐ ω ∂P, Continuous (X · ω)

/-! ## 5. The theorem -/

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
  sorry

end BrownianMotionChallenge
