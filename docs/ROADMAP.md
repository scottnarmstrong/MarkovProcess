# Roadmap

What the library will contain next, in dependency order, with the statement each item delivers.
Every item is generic: it mentions no coefficient, no partial differential equation, and no
particular model. Items are listed in the order they can be built; an item's prerequisites are
the items above it that it names.

## 1. The generator of the generated semigroup (Hille–Yosida identification)

For a contractive resolvent `R` (`Semigroup/ContractiveResolvent.lean`) and its generated
semigroup `S := R.generatedSemigroup`, the generator of `S` is the operator `L` with
`R_μ = (μ − L)⁻¹`: `S.generatorDomain = range (R.operator μ)` for every `μ > 0`,
`L (R_μ g) = μ R_μ g − g`, and `R_μ (μ f − L f) = f` on the domain. Consequences: orbits of
domain elements are differentiable (two-sided), and **the generator determines the semigroup**:
two strongly continuous contraction semigroups with the same generator are equal.

*Status: landed* (`Semigroup/GeneratorResolvent.lean`, `Semigroup/GeneratorInjectivity.lean`,
`Semigroup/GeneratorUniqueness.lean`), together with the converse half: the resolvent of a
semigroup as the Laplace transform of its orbits, the closedness of the generator, and both round
trips between semigroups and contractive resolvents (`Semigroup/Resolvent.lean`,
`Semigroup/GeneratorClosed.lean`, `Semigroup/ResolventGeneration.lean`).

## 2. The killed process on lifetime paths

`killAtExit U : ContinuousPath α → LifetimePath U` (lifetime the exit time, live path the path
inside `U`), the kernel `killedProcess : Kernel U (LifetimePath U)`, its lifetime law and
one-time marginals, and the identification of its finite-dimensional distributions with the
cemetery extension of the killed semigroup (`Killed/Semigroup.lean`,
`DenseTime/CemeterySemigroup.lean`). Then the part-process property for nested open sets
`U ⊆ V`: the `U`-killed process of the `V`-killed process is the `U`-killed process.

*Status: landed* (`Killed/KillAtExit.lean`, `Killed/Process.lean`, `Killed/Marginals.lean`,
`Killed/Nested.lean`); the part-process property is stated through the inclusion of the carriers
`U ⊆ V`, at the level of the finite-dimensional distributions.

## 3. Exit laws and the killed resolvent

The stopped law `x ↦ law of (T ω, ω (T ω))` as a kernel into `NNReal × α` for a finite
stopping time `T`, and the exit distribution (harmonic measure) of an open set on the event that
the path leaves it; the killed resolvent
`R^U_λ f (x) = E_x ∫_0^{τ_U} e^{−λt} f(ω_t) dt` as the Laplace transform of the killed kernels.

*Status: landed* (`Trajectory/ExitLaw.lean`, `Killed/Resolvent.lean`).

## 4. Harmonic and Poisson representations; the localized Dynkin formula

For `f` in the generator domain: if `L f = 0` on an open `U` then `f x = E_x f(ω_{τ_U ∧ K})`;
if `L f = −g` on `U` then `f x = E_x f(ω_{τ_U ∧ K}) + E_x ∫_0^{τ_U ∧ K} g(ω_s) ds`; and the
localized form of Dynkin's formula for a continuous function that agrees with a domain element on
the closure of `U`, which is how test functions that are not in `C₀` (such as squared distances)
enter moment identities.

*Status: landed* (`Trajectory/HarmonicRepresentation.lean`).

## 5. Exhaustions, the minimal semigroup, and nonexplosion

Along every continuous path the exit times of an increasing open exhaustion `U_n ↑ α` tend to
infinity. From a compatible family of killed semigroups on an exhaustion (each the part process
of the next), the monotone limit is a sub-Markov kernel semigroup, the **minimal semigroup**; it
is conservative exactly when the exit times of the exhaustion are almost surely unbounded from
every starting point (the nonexplosion criterion), and it is then the semigroup of the whole
process.

*Status: the path-space statement and the limit of the killed kernels are landed*
(`Path/Exhaustion.lean`, `Killed/Minimal.lean`: along an open exhaustion the killed kernels increase
to the transition kernels); the abstract minimal semigroup built from a compatible family of killed
semigroups is open.

## 6. Tightness on path space and weak continuity of the law

From the Kolmogorov moment criterion, uniform in the starting point, the family of laws
`{Q x}` is tight on `C([0, ∞), α)` (uniform moment bounds on a Hölder modulus, Arzelà–Ascoli);
hence `x ↦ Q x` is weakly continuous on path space, extending the cylinder-expectation
continuity of `Trajectory/StartingPointContinuity.lean`. The route is direct: on a compact set
of paths, cylinder functions are dense among continuous functions (Stone–Weierstrass), so
tightness reduces weak continuity to the cylinder case; no compactness theorem for measures is
needed.

*Status: landed* (`Continuity/DyadicPathChaining.lean`, `Continuity/PathModulus.lean`,
`Continuity/PathTightness.lean`, `Trajectory/PathModulus.lean`, `Trajectory/PathTightness.lean`,
`Trajectory/CylinderAlgebra.lean`, `Trajectory/WeakContinuity.lean`). The modulus estimate is
uniform in the starting point; tightness is stated over compact sets of starting points and, for
the Arzelà–Ascoli step, on a proper state space; weak continuity of `x ↦ Q x` into the space of
probability measures on path space follows.

## 7. Convergence of Feller processes

Trotter–Kato: for strongly continuous contraction semigroups on one Banach space, convergence of
the resolvents at one positive shift gives strong convergence of the semigroups, uniformly on
bounded time intervals, and conversely; convergence of Feller kernel semigroups gives
convergence of finite-dimensional distributions of the processes; together with tightness
(item 6), weak convergence of the processes on path space.

*Status: landed* (`Semigroup/TrotterKato.lean` for both directions between semigroup and
resolvent convergence on one space; the different-space Trotter–Kurtz theorem is not stated; `Feller/FiniteTimeConvergence.lean` and `Feller/FiniteSetConvergence.lean`
for the finite-dimensional laws; `Trajectory/Convergence.lean` for the processes;
`Trajectory/WeakConvergence.lean` for weak convergence on path space under one common Kolmogorov
moment bound). No Prokhorov theorem is used: tightness is proved directly from the common moment
bound and weak convergence is reduced to the finite-dimensional case by cylinder approximation on
a compact set of paths, as in item 6. Brownian motion is available as a limit object from item 9
onwards; no invariance principle is stated.

## 8. Small generalizations

Equivariance between two different state spaces (a homeomorphism `α ≃ₜ β`), and the
identification of the generator domain of the `C₀` semigroup of a Feller kernel semigroup with
the range of its resolvent, restated on the kernel side.

*Status: landed* (`FiniteTime/KernelEquivariance.lean`, `Trajectory/Equivariance.lean`,
`Parameterized/Equivariance.lean` for the equivariance; `Feller/Resolvent.lean` for the kernel-side
resolvent and the domain identification).

## 9. Brownian motion

The heat semigroup on the line, whose transition measure at time `t` from `x` is the Gaussian law
with mean `x` and variance `t`, as a conservative Feller semigroup satisfying the Kolmogorov
moment criterion with `p = 4`, `q = 2`; its continuous-path process `brownianMotion`; and the
identification of the canonical process under `brownianMotion x`, recentred at `x`, as a Brownian
motion: centred Gaussian marginals, independent increments over the consecutive intervals of every
finite monotone family of times, and continuous trajectories.

*Status: landed* (`Examples/HeatSemigroup.lean`, `Examples/BrownianMotion.lean`). Covered: one
space dimension; the simple Markov property in joint-law form
(`brownianMotion_map_prodMk_shift`), from which the product form of the law of the increments
follows by induction, for merely monotone families of times and not only strictly increasing ones;
uniqueness of the process among Markov kernels with the Gaussian finite-dimensional distributions.
Not covered: the multidimensional heat semigroup, which waits for a multivariate Gaussian law in
Mathlib; the Lévy characterization, quadratic variation, and stochastic integration.
`HasIndepIncrements` is Mathlib's definition copied verbatim, and `IsBrownianReal` is the form
that Mathlib proves equivalent to its own projective-family definition; neither is available at
the pinned revision.
