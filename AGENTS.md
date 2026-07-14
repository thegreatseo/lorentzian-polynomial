# Repository guide

This repository formalizes Lorentzian polynomials in Lean 4 using mathlib. Keep changes focused,
readable, and suitable for eventual mathlib-style review.

## Project layout

- `LorentzianPolynomial.lean` is the library root and currently re-exports
  `LorentzianPolynomial.ClosureProperty`.
- `LorentzianPolynomial/MConvex.lean` defines `Set.MConvex`.
- `LorentzianPolynomial/Basic.lean` defines the core Lorentzian-polynomial predicates and proves
  the equivalence with the recursive characterization.
- `LorentzianPolynomial/ClosureProperty.lean` proves closure under elementary variable splitting.
- `lakefile.toml`, `lean-toolchain`, and `lake-manifest.json` define the build and dependency pins.
- `.github/workflows/lean_action_ci.yml` runs the full build in CI. There is no separate test suite.

Imports follow the dependency order `MConvex` -> `Basic` -> `ClosureProperty` -> library root. Avoid
cycles, and add a new public module to the appropriate import chain.

## Toolchain and commands

- Lean: `v4.32.0` (`leanprover/lean4:v4.32.0`).
- mathlib: `v4.32.0`, resolved by the manifest to commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Full build and test: `lake build`
- Focused check while editing: `lake env lean LorentzianPolynomial/<File>.lean`

Run commands from the repository root. Since the project has no test target or test directory,
`lake build` is the required final verification and matches CI. Do not edit generated Lake state or
dependency pins unless the task specifically requires a toolchain or dependency change.

## Lean and mathlib style

- Use the mathlib-style structure demonstrated by `ClosureProperty.lean`: a valid copyright and
  license header, `module`, minimal `public import`s, then the module docstring before other
  commands, `@[expose] public section`, and the narrowest useful namespace/section. Do not copy the
  placeholder release text currently present in `Basic.lean` and `MConvex.lean`.
- Follow nearby mathlib formatting and naming: predicates and definitions use established Lean
  naming, theorem and lemma names are descriptive, and namespaced declarations expose their
  subject. Wrap long declarations and proofs for readability; no formatter is configured.
- Add `/-- ... -/` documentation to public definitions and theorems. Keep implementation helpers
  `private` when they are not part of the API.
- Keep imports minimal and ordered before declarations. Prefer reusing mathlib declarations over
  duplicating general-purpose facts locally.
- `relaxedAutoImplicit = false` is enabled, so declare variables and types explicitly. The project
  also enables `weak.linter.mathlibStandardSet`; do not add warnings, and fix warnings in touched
  code when they are in scope rather than suppressing them without a clear reason.
- Use `noncomputable section`, `classical`, `omit`, and local instances only where needed, at the
  narrowest scope. Match the surrounding use of Unicode Lean notation.

## Proof development

- State useful intermediate facts as small, well-named lemmas. Split long tactic blocks around the
  mathematical steps so hypotheses, transformations, and the final goal remain easy to follow.
- Prefer stable, targeted proof steps (`rw`, `simp`/`simp only`, `exact`, `refine`, structured
  induction and case splits) and existing mathlib lemmas. Use automation such as `omega`,
  `positivity`, or `grind` when it makes the argument clearer, not as a substitute for structure.
- Keep theorem statements general and assumptions minimal. Preserve the current namespace API and
  avoid making helper declarations public merely to finish a proof.
- During development, check the edited module with `lake env lean ...`; then run `lake build` to
  catch downstream import failures and lint warnings.
- Do not leave `sorry`, `admit`, placeholder axioms, debug commands, or exploratory declarations in
  committed code.

## Final verification

Before handing off a Lean change:

1. Run a focused check for every edited Lean module.
2. Run `lake build` from the repository root.
3. Review all warnings and the diff; ensure imports, documentation, and proof structure match the
   surrounding mathlib style and that no unrelated or generated files changed.

The current build succeeds but has pre-existing `Basic.lean` warnings about its placeholder header,
missing module docstring, and one unused `DecidableEq` assumption. Treat these as cleanup targets,
not style precedent, and do not increase the warning baseline.
