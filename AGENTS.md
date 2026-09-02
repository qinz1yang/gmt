# GMT - Codex instructions

This is a Lean 4 and Mathlib library for Euclidean geometric measure theory. Its intended scope
includes normalized Hausdorff measure, area and coarea, rectifiable sets, BV and finite perimeter,
varifolds, Allard regularity, currents, area-minimizing currents, and their reusable analytic and
linear-algebraic foundations. Reusable mathematics is the product; applications are thin capstones.

## Authorities and evidence

- `NAMING.md` is the authority for declaration names. `STRUCTURE.md` is the authority for files,
  folders, granularity, variants, and placement. Read both in full before adding, renaming, moving,
  or reorganizing public mathematics.
- This file governs workflow, soundness, elaboration quality, and delivery gates.
- The exact on-disk Lean declaration, its proof body, the compiler, and its transitive axiom closure
  outrank comments, commit messages, plans, search summaries, remembered APIs, and agent reports.
- Inspect the current worktree before editing. Preserve unrelated and user-owned changes.

## Mathematical architecture

1. Keep the Euclidean GMT core independent of DifferentialGeometry. Library source may depend on
   Mathlib and explicitly vendored packages, but must not import the DifferentialGeometry project.
2. Use Mathlib's normalized Euclidean Hausdorff measure `μHE`, rectangular linear-map
   `normDet`, covering, differentiation, Radon-measure, and Riesz representation infrastructure
   rather than cloning it. Prove the explicit bridge to Simon's normalization when that exact
   constant identity is needed.
3. Build one dependency forest: measure and linear foundations first; area and coarea next;
   rectifiability and BV above them; general varifolds before rectifiable and integral
   specializations; currents over the shared area and rectifiability layer; regularity over the
   corresponding geometric objects and dry analysis.
4. Treat general varifolds as the primary objects. Rectifiable and integral varifolds are natural
   specializations or represented properties, not alternative foundational definitions.
5. Treat geometric analysis as a first-class library component. Sobolev, harmonic, elliptic,
   compactness, approximation, iteration, and decay results belong in reusable analytic homes rather
   than inside Allard or minimizing-current proofs.
6. Keep Riemannian and manifold GMT out of this repository unless the project scope is explicitly
   enlarged. Compatibility with DifferentialGeometry belongs downstream.
7. Maintain `External/` as vendored third-party mathematics. Preserve upstream provenance,
   licenses, attribution, original documentation, and citation metadata; record every local source
   modification in the vendor's modification log.

Placement is mathematical, not line-count driven:

- One coherent development, however long, is one file.
- A definition with an API and several separable developments is a concept folder, normally
  `Defs.lean`, `Basic.lean`, and mathematically named aspect files.
- Split only across genuine mathematical interfaces. Compile-time improvements may motivate a split
  only when those interfaces are real; never slice a proof by arbitrary line count.
- Use precise imports and preserve the dependency direction in `STRUCTURE.md`.
- `GMT.lean` is the single flat root aggregate. Do not create per-folder aggregators.
- Namespaces follow mathematical objects and remain decoupled from paths.

For variants, follow the conclusion:

- Different conclusions are coequal siblings sharing their common foundations.
- The same conclusion with stronger assumptions or a special object is a corollary of the natural
  general primary theorem.
- Development may proceed through a special case, but the final public API exposes the mathematically
  natural direction.

## Public API design

- Use standard, widely recognized GMT vocabulary. Theorem names are snake case; definition,
  structure, class, and abbreviation roots follow Mathlib casing.
- Name classical results by accepted names only when the exact statement is present.
- Never expose task history, effort words, node identifiers, arbitrary numbering, invented
  abbreviations, or proof routes in public names.
- Search this library and Mathlib by mathematical content, type shape, and several standard name
  variants before creating anything. Read every plausible signature and inspect its axioms.
- Reuse and generalize an existing canonical declaration instead of cloning it. Re-export when only
  visibility is missing.
- State the weakest natural theorem, not merely the weakest theorem one current consumer needs.
- Prefer intrinsic finite-dimensional real inner-product-space formulations. Coordinate and matrix
  versions are computational corollaries unless coordinates are mathematically essential.
- Minimize typeclass assumptions. Construct stronger instances locally when only the proof needs
  them.
- Preserve established public signatures when compatibility is material. Make breaking
  generalizations deliberately and update all consumers coherently.

## Source discipline

- Write zero comments and zero docstrings in non-vendored Lean source. Preserve required existing
  Apache Copyright and Authors headers; add no new per-file copyright headers.
- New source files begin with imports. There is no module docstring after them.
- On-disk identifiers and code are English. User-facing discussion may use another language.
- Preserve exact `variable`, `open`, `omit`, `include`, `attribute`, `noncomputable`, and
  local-instance scopes when moving code.
- Keep namespace openings minimal and lexical. Prefer qualified names, selective openings, or
  declaration-local openings over broad namespace openings.
- Before making a private declaration public, verify its proposed full name is unique library-wide.
- Do not commit exploratory `#check`, `#print`, `#eval`, `#reduce`, trace options,
  `logInfo`, tactic suggestions, or diagnostic output.
- Keep scratch probes outside the project tree and remove them after use.

## Soundness

A green build is necessary but not sufficient.

- Never package the conclusion as a hypothesis or return an equivalent hypothesis.
- Every predicate must genuinely constrain its advertised object. Check existential packages against
  zero, constant, empty, full-space, zero-multiplicity, and unrestricted witnesses.
- Do not turn an existentially produced plane, tangent, multiplicity, measure, orientation, or
  representative into a free universal input without the equation tying it to its producer.
- Match domains and quantifiers to the hypotheses. Distinguish pointwise from almost-everywhere,
  local from global, rectifiable from purely unrectifiable, and weak from strong convergence.
- Fix Hausdorff normalization before using density ratios, monotonicity constants, mass ratios, or
  Allard smallness hypotheses. Never silently mix `μH`, `μHE`, and an explicitly scaled measure.
- Keep dimension and codimension hypotheses explicit. Do not use a square determinant where a
  rectangular norm determinant or tangential Jacobian is required.
- A moving approximate tangent plane must be measurable before it is integrated. A raw choice of
  tangent planes is not automatically a measurable field.
- Do not define stationarity by assuming the desired monotonicity or regularity conclusion. Do not
  define rectifiability by packaging a representation theorem as input.
- For currents, distinguish norm and comass, preserve orientation and sign conventions, and verify
  boundary, restriction, product, pushforward, and slicing dimensions exactly.
- New `sorry`, `admit`, `axiom`, `trustMe`, or proposition-valued hypothesis packaging is
  forbidden unless the owner explicitly authorizes a transient proof frontier.
- For every completed headline, verify that its axiom closure contains no `sorryAx` and only
  owner-approved foundational axioms.

## Linters, generality, and elaboration performance

- The Mathlib standard linter set, excluding the documentation-presence linters `docBlame` and
  `docBlameThm`, is a delivery gate.
- Never add `@[nolint ...]`, `attribute [nolint ...]`, or any global, file-local, or
  declaration-scoped linter disable. Repair the declaration or proof instead.
- Resolve `unusedSectionVars` with `omit`, a smaller variable block, or a more general statement.
- Treat unused instances and binders as API-review findings. Remove or weaken them when compatible.
- Keep `classical`, `DecidableEq`, coordinates, bases, finite enumerations, and synthesized finite
  structures local when they are proof devices rather than mathematical hypotheses.
- Do not submit `maxHeartbeats`, `maxRecDepth`, or synthesis-heartbeat budget overrides. Refactor
  the proof or expose a genuine reusable lemma.
- An elaborator-semantics option may remain only when genuinely required, narrowly scoped, and not
  used as a resource budget or diagnostic suppressor.

## Workflow and delivery gate

- During development, build the changed module by its Lean module name after each coherent edit. Run
  broader dependent builds after changing a public signature or module boundary.
- Git commits and pushes of in-scope work are owner-authorized. Make proactive checkpoint commits
  after each dependency-closed, compile-clean mathematical layer, before a risky refactor, after
  closing a headline, and after the final delivery gate.
- Before every checkpoint, inspect the worktree and complete diff, stage only intended files, and
  exclude scratch probes, diagnostics, generated noise, unrelated changes, and known broken states.
- Before handoff, build every changed module and run `lake build GMT` after the final edit.
- Final output contains zero errors and zero warnings except owner-approved warnings from explicitly
  retained transient proof frontiers. It contains no avoidable diagnostics or tactic suggestions.
- Run `git diff --check`. Review the complete diff for mathematical correctness, normalization,
  generality, duplicated APIs, placement, imports, hidden assumptions, vacuity, diagnostics, comments,
  resource overrides, and dead code.
- Register every new public leaf in `GMT.lean` and verify that the root build reaches it.
- Do not claim a theorem proven from reading, a compiling decomposition, or a clean grep. The proof
  certifies the leaf; compiled glue certifies assembly; axiom closure certifies transitive completion.

For a curated family of related classical results, use the `prove-theorem-suite` workflow. Project
standards in this file remain binding.
