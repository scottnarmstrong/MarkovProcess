# Contributing to MarkovProcess

These are the project's hard rules. They are not style preferences to be traded away under
schedule pressure: each one exists because violating it has, in practice, hidden a real problem.
A change that breaks one of them will not be merged, however good the mathematics.

## Elaboration budget

**Never use `set_option maxHeartbeats`, or any other heartbeat-budget override, anywhere in the
tree.** A proof that will not elaborate at the default heartbeat budget is telling you something
about its design — a hypothesis in the wrong form, a typeclass search that is being redone at
every step, a lemma that should have been split out — and the correct response is to refactor or
split it. Raising the budget hides the signal and pushes the cost onto everyone who imports the
file. If you cannot get a proof under the default budget, report it as a design signal and ask,
rather than silencing it.

The same applies to `set_option synthInstance.maxHeartbeats`, `maxRecDepth` raised to mask a
loop, and any other resource dial used to make a failure go away rather than to diagnose it.

## File size and scope

- **No Lean file may exceed 1500 lines.** This is a hard cap, checked in CI.
- **Prefer files under 800 lines.** Every file over 800 lines should have a reason you can state
  in one sentence.
- **One focused topic per file.** A file's module docstring should be able to name its subject in
  a single title line and describe it in one or two sentences. If it cannot, the file is doing
  two things and should be split.
- When splitting, keep the public import paths that consumers already use, as thin facade
  modules re-exporting the new pieces, rather than breaking every downstream import at once.

## Soundness

- **No custom axioms.** Do not introduce an `axiom` declaration under any circumstance.
- **No `sorry`**, in any form, including `sorryAx`, admitted `example`s, or a `sorry` "temporarily"
  parked behind a comment. CI rejects the string.
- **Every new public theorem must pass an axiom check.** Run `#print axioms YourTheorem` in a
  probe file outside the library tree and confirm the output is exactly
  `'YourTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]`, or a subset of
  those three. Anything else — a stray axiom, a `sorryAx`, an unexpected dependency — is a
  blocking defect. Note the check in the pull request.

## Instances

**Every `local instance` must be named.** Anonymous ones export auto-generated names derived from
the instance type, so two files that both write

```lean
local instance : MeasurableSpace (ContinuousPath alpha) := borel _
```

produce colliding declaration names once both are imported. Give each one a name that includes
the file or theorem context, for example
`fellerStoppingRestartMeasurableSpaceContinuousPath`. The same reasoning applies to any
anonymous instance introduced in more than one place.

## Statements are frozen

**A statement never changes for performance, convenience, or to make a proof go through.** If a
proof is hard, fix the proof. If the statement is genuinely wrong or genuinely too weak, that is
a separate, deliberate change: propose it on its own, explain what the new statement says that
the old one did not, and update every consumer in the same commit. A performance commit that
also edits a theorem statement will be rejected on sight.

Weakening a hypothesis, strengthening a conclusion, and renaming are all statement changes for
this purpose. A commit whose message begins `perf(` must leave every `theorem` and `def`
signature byte-identical.

## Tactic discipline

- **`simp only` with an explicit lemma list**, not bare `simp`. Bare `simp` is a moving target:
  it changes behaviour when Mathlib's simp set changes, and it hides which lemma actually did the
  work. The `unusedSimpArgs` linter is on, so an over-long list will be flagged.
- **`linarith only [...]`** with the hypotheses you mean, rather than bare `linarith`; likewise
  `nlinarith only [...]`, `omega` over the smallest context you can arrange, and named `gcongr`
  side goals. `nlinarith` in particular is expensive and should be replaced by an explicit
  `calc` whenever the inequality has a readable proof.
- Avoid closers that search (`fun_prop` and `measurability` for measurability goals are fine): prefer an explicit term or `exact?`-discovered lemma name to
  `aesop` or `decide` in committed code, unless you have profiled the alternative
  and it is worse.

## Documentation

- **Every public declaration carries a docstring** — every `theorem`, `def`, `structure`,
  `abbrev`, and named `instance` that is not `private`. State what the declaration says, not how
  it is proved.
- **Every file begins with a copyright header and a module docstring** in the Mathlib shape: a
  `/-! # Title -/` block naming the file's subject, then one or two sentences describing what it
  establishes. Where the file's result is conditional on a hypothesis, or deliberately does not
  claim something a reader might expect, say so in the module docstring.
- Docstrings describe the mathematics. They do not describe the development process, the review
  status, or who asked for the file.

## Build hygiene

- **The lakefile's lint options must pass with zero diagnostics.** The library sets
  `autoImplicit := false`, `relaxedAutoImplicit := false`, and enables the `unusedVariables`,
  `unusedSectionVars`, `unusedSimpArgs`, `unnecessarySimpa` and `deprecated` linters. A green
  build means zero errors *and* zero warnings.
- Do not add a dependency. Mathlib, pinned in `lake-manifest.json`, is the only one, and the
  library must never require another repository.
- Do not commit anything under `.lake/`.

## Performance changes

A change made for elaboration speed requires **a measured A/B profile, before and after**:

1. Profile the file as it stands: `lake env lean --profile MarkovProcess/Path/Yours.lean`,
   serial, on a warm build, taking the minimum of three runs.
2. Make the change.
3. Profile again the same way.
4. Keep the change **only on a measured win**: the targeted phase (typeclass inference,
   elaboration, tactic execution) drops by at least ten percent and no other phase gets worse by
   more than that. Revert anything that does not clear the bar, including changes that lower one
   phase while raising total wall clock.
5. Record both numbers in the commit message.

An unmeasured "this should be faster" is not a performance change; it is an untested refactor of
working code: a clean project-only rebuild timed with `/usr/bin/time -v lake build`, per-module
times read from the `Built MarkovProcess.* (Ns)` log lines, and a warm own-file profile
(`lake env lean --profile <file>`) of any module that stands out.

## Pull request checklist

- [ ] `lake build` is green: zero errors, zero warnings, under the lakefile's lint options.
- [ ] No `sorry`, no `axiom`, no `maxHeartbeats` or other heartbeat override.
- [ ] Every file under 1500 lines; new files preferably under 800.
- [ ] `#print axioms` on each new public theorem shows only `propext`, `Classical.choice`,
      `Quot.sound`; the output is quoted in the PR.
- [ ] Every new public declaration has a docstring; every new file has a copyright header and a
      module docstring.
- [ ] Every new `local instance` is named.
- [ ] No theorem or definition statement changed, unless the PR is explicitly a statement change
      and says so in its title.
- [ ] Any performance change carries its before/after profile numbers.
