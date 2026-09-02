import Lake

open Lake DSL

package «MarkovProcess» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

/-- The comparator surface (`Audit/*/Challenge.lean`, `SolutionBasic.lean`, `Solution.lean`).
Not a default target: build on demand with `lake build Audit`. -/
lean_lib «Audit» where
  globs := #[.submodules `Audit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

@[default_target]
lean_lib «MarkovProcess» where
  globs := #[.andSubmodules `MarkovProcess]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]
