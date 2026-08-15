# Physlib Lean code check

Use this to review the Lean code itself before a PR.

## 1. Find the right structure

- [ ] Identify the most general mathematical object actually used by the result.
- [ ] Do not name the central structure after only one physical interpretation.
- [ ] Separate the reusable mathematical structure from physical specializations.
- [ ] Prefer an existing Mathlib structure over a custom replacement.
- [ ] Search Mathlib and Physlib before defining anything substantial:

  ```sh
  rg "Name|RelatedConcept" .lake/packages/mathlib/Mathlib Physlib -g '*.lean'
  ```

- [ ] Bundle laws that define the object. Do not repeatedly pass the same group, continuity, or
      unitarity hypotheses to every lemma.
- [ ] Use existing subtypes when they encode the required invariant. For example, use Mathlib's
      unitary subgroup instead of an operator plus a separate proof of unitarity.
- [ ] Put assumptions on the smallest possible layer. A physics specialization may assume more than
      the general mathematical result.
- [ ] Check that the assumptions match the claimed scope:
  - finite-dimensional or arbitrary dimension;
  - bounded or unbounded operators;
  - norm-continuous or strongly continuous maps.
- [ ] Choose the common user-facing coercion carefully. Routine expressions should be short and
      should not require repeated subtype casts.

## 2. Delete redundant code

- [ ] Delete structures that only rephrase an existing Mathlib structure.
- [ ] Delete definitions that merely rename a field or a one-line existing construction.
- [ ] Delete wrapper lemmas already available from the bundled structure.
- [ ] Delete state-level versions of operator equalities when ordinary simplification already proves
      them.
- [ ] Delete specializations that are immediate applications of a more general theorem unless they
      add real physics meaning or improve usability.
- [ ] Delete helper declarations used only once when inlining makes the proof clearer.
- [ ] Keep a helper lemma when it expresses an independently meaningful identity or makes a long
      proof substantially easier to understand.
- [ ] Delete unused instances, aliases, notation, imports, examples, and temporary files.
- [ ] Delete an entire file when its contents are redundant or no longer connected to the main API.
- [ ] Search for downstream uses before deleting:

  ```sh
  rg "DeclarationName|File.Module.Name" Physlib QuantumInfo -g '*.lean'
  ```

## 3. File and namespace organization

- [ ] Name a file after its main definition, not after one theorem proved inside it.
- [ ] Put general mathematics under the appropriate mathematics directory.
- [ ] Put Hamiltonian, momentum, rotation, or time-evolution terminology only in the physical
      specialization where that interpretation is present.
- [ ] Keep each file centered on one coherent concept.
- [ ] Every declaration belongs naturally beside the surrounding declarations.
- [ ] Namespaces match the object being developed.
- [ ] New files are imported by the appropriate root file and the import remains sorted.
- [ ] Module documentation describes the actual final API, not deleted earlier versions.

## 4. Public API design

- [ ] A user can construct the main object directly from the natural input.
- [ ] A user can state and invoke the main result without cumbersome casts or implementation details.
- [ ] Expose the canonical object directly when possible, for example `generator`, rather than only
      an existential statement such as `∃! generator, ...`.
- [ ] Split a large existential theorem into a usable API:
  - a definition of the canonical object;
  - a lemma proving its defining property;
  - a lemma proving uniqueness;
  - a converse constructor;
  - an equivalence if both directions are useful.
- [ ] Physical specialization lemmas explain the connection explicitly. For example, time evolution
      should state that its group generator is `H / ℏ` and derive `exp (-itH/ℏ)` from the general
      theorem.
- [ ] Avoid exporting technical proof helpers unless they are reusable mathematical facts.
- [ ] Add an extensionality lemma only when equality of the bundled structure is genuinely needed.

## 5. Lemma versus theorem

- [ ] Use `lemma` by default in Physlib.
- [ ] Use `theorem` only for a major result conventionally known as a theorem in physics or
      mathematics, and only if that distinction is useful in the file.
- [ ] Do not alternate between `lemma` and `theorem` merely based on proof length.
- [ ] Important lemmas and all definitions have concise docstrings.
- [ ] Names describe mathematical content, not proof strategy.
- [ ] Avoid names such as `helper`, `aux`, `temp`, or numbered variants in the public API.

## 6. Simplify proof structure

- [ ] Keep proofs under roughly 50 lines where possible.
- [ ] Split long proofs along mathematical meaning, not arbitrary line count.
- [ ] Extract a standalone lemma when a proof establishes an independently useful fact.
- [ ] Extract general mathematics before proving the physical specialization.
- [ ] Use a `calc` block for a chain of equalities or inequalities.
- [ ] Avoid alternating many small `have` and `rw` steps when one calculation tells the story better.
- [ ] Reserve `have` for facts that deserve a name and are used later.
- [ ] Remove a `have` that only renames a hypothesis or repeats a one-line expression.
- [ ] Pull repeated expressions into one meaningful `let` or definition.
- [ ] Do not introduce a `let` that merely gives an existing hypothesis another name.
- [ ] Simplify trivial branches with standard lemmas such as `Subsingleton.elim`.
- [ ] Prefer a direct `simp`, `simpa`, `rw`, `module`, `ring`, or `noncomm_ring` proof when it remains
      readable.
- [ ] Search for existing cancellation, inverse, adjoint, exponential, continuity, and
      self-adjointness lemmas before proving algebra manually.
- [ ] Avoid unfolding a high-level structure when its API already proves the needed result.

## 7. Hypotheses and types

- [ ] Every hypothesis is used.
- [ ] Hypotheses are no stronger than necessary.
- [ ] Typeclass assumptions are placed compactly and consistently.
- [ ] Do not install a local instance that Lean already obtains from a branch or hypothesis.
- [ ] Avoid unnecessary finite-dimensional assumptions when the proof works for bounded operators on
      an arbitrary Hilbert space.
- [ ] Do not claim the unbounded form of a result when the implementation uses continuous linear maps
      and operator-norm continuity.
- [ ] Check signs and scalar conventions manually, especially factors of `Complex.I`, `-1`, and `ℏ`.

## 8. Coercions and notation

- [ ] The most common expression has the simplest syntax, such as `U t` rather than repeated casts.
- [ ] Coercions do not hide an incorrect invariant or change the mathematical meaning.
- [ ] Use a small adapter definition only when it genuinely connects two existing APIs.
- [ ] Add a simp lemma for the adapter's application when that is a normal projection reduction.
- [ ] Do not create notation unless it is used repeatedly and improves readability.
- [ ] Test the public API in one small runnable example.

## 9. Simp discipline

- [ ] Add `@[simp]` only when the right-hand side is a clear normal form.
- [ ] Projection, identity, inverse/adjoint, and constructor-application lemmas are often good simp
      lemmas.
- [ ] Expansive formulas are usually bad simp lemmas. In particular, do not globally rewrite every
      abstract group value into a large exponential expression.
- [ ] If `simpNF` reports that an earlier lemma is rewritten by a later simp lemma, remove or rethink
      the aggressive simp attribute instead of adding `@[nolint simpNF]` automatically.
- [ ] Run the declaration linter after changing any simp attribute:

  ```sh
  lake exe runPhyslibLinters Physlib
  ```

## 10. Imports

- [ ] Temporarily run `#min_imports` at the bottom of every changed Lean file.
- [ ] Remove `#min_imports` afterward.
- [ ] Do not trust only an isolated file check; stale `.olean` files or transitive imports can hide a
      missing direct import.
- [ ] Run the full build after changing imports.
- [ ] Avoid importing a large physics module solely to obtain a small mathematical fact.
- [ ] Keep public imports minimal and intentional.

## 11. Documentation check

- [ ] The overview states exactly what is proved.
- [ ] The overview distinguishes the bounded/norm-continuous result from the full unbounded/strongly
      continuous theorem.
- [ ] The key-results list contains declarations that still exist.
- [ ] No documentation references deleted files, renamed declarations, or obsolete conventions.
- [ ] Comments explain mathematical choices, not obvious syntax.
- [ ] Remove filler, defensive prose, development history, and claims that are not used by the file.

## 12. Final Lean checks

- [ ] Compile every changed file directly:

  ```sh
  lake env lean Physlib/Path/ChangedFile.lean
  ```

- [ ] Build the whole library:

  ```sh
  lake build
  ```

- [ ] Run declaration linters:

  ```sh
  lake exe runPhyslibLinters Physlib
  ```

- [ ] Run the complete linter suite:

  ```sh
  lake exe lint_all
  ```

- [ ] Run style checks:

  ```sh
  ./scripts/lint-style.sh
  ```

- [ ] Check patch formatting:

  ```sh
  git diff --check
  git diff --cached --check
  ```

- [ ] Search the changed files for forbidden or suspicious leftovers:

  ```sh
  rg "sorry|axiom|private|TODO|helper|aux" CHANGED_FILES
  ```

- [ ] Read the complete final diff once more, declaration by declaration.
- [ ] Confirm that all temporary files, experiments, obsolete modules, and redundant declarations are
      gone.
