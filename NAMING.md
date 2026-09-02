# NAMING.md - public declaration names

This file is the authority for declaration names in `GMT`. `STRUCTURE.md` governs file and folder
placement. `AGENTS.md` governs workflow, soundness, source discipline, and delivery. The exact
elaborated declaration remains the final authority for what a name denotes.

## 1. Search before naming

Before adding or renaming public mathematics:

1. Search Mathlib and this library by mathematical content, type shape, and several standard names.
2. Read every plausible signature and inspect its axiom closure.
3. Reuse, generalize, or re-export the canonical declaration when possible.
4. Check the proposed fully qualified name for collisions.

Do not create a second vocabulary for an object already named in Mathlib. In particular, do not
shadow `Measure.euclideanHausdorffMeasure`, `μHE`, `LinearMap.normDet`, or the existing
covering and differentiation APIs.

## 2. Casing by declaration kind

- Theorems and lemmas use lower snake case.
- Value- and function-valued `def` and `abbrev` names use lower camel case.
- Type-valued definitions and abbreviations use Upper camel case.
- `structure`, `class`, and `inductive` names use Upper camel case.
- Namespaces use Upper camel case and name mathematical objects or subjects.
- Preserve established Mathlib identifier tokens inside theorem names when appropriate.

Local implementation lemmas follow the same rules. A private declaration may have a concise
technical name, but making it public requires a mathematical name and a library-wide collision check.

## 3. Name the mathematical result

Use standard GMT vocabulary. A classical name is appropriate only when the public signature states
the accepted theorem with natural hypotheses. Examples include:

- `area_formula` and `coarea_formula`;
- `de_giorgi_structure`;
- `allard_regularity`;
- `federer_fleming_compactness`;
- `monotonicity` within a namespace whose object makes the result unambiguous.

If a result is only a conditional core, name the supplied condition or object that drives it. A
theorem assuming a preconstructed graphical representation is not itself Allard regularity. A
compactness theorem assuming a convergent subsequence is not Federer-Fleming compactness.

For results without an accepted eponym, describe the conclusion and only essential disambiguating
hypotheses:

```text
subject_conclusion_of_essential_hypotheses
```

Do not encode the proof route in the name.

## 4. Main object namespaces

Operations and laws belong in the namespace of their principal mathematical object when this makes
names shorter and discoverable. Natural examples include:

- `Varifold.weightMeasure`, `Varifold.firstVariation`, and `Varifold.pushforward`;
- `Current.mass`, `Current.boundary`, and `Current.restrict`;
- `RectifiableSet.approxTangent`;
- `FinitePerimeter.reducedBoundary`.

The final names must follow the exact representations chosen by the formalization and existing
Mathlib precedent. These examples are vocabulary guidance, not pre-approved declarations.

## 5. Hypotheses and variants

- Use an `of_...` suffix only for load-bearing mathematical hypotheses.
- Do not list routine typeclass assumptions or implementation devices in a name.
- Different conclusions are coequal siblings over shared foundations.
- The same conclusion under stronger assumptions is a corollary of the natural primary theorem.
- General, rectifiable, integral, stationary, oriented, local, global, boundary, pointwise,
  integrated, and scale-normalized variants receive qualifiers only when the distinction is
  mathematically real.
- Distinguish equality, absolute continuity, inequality, convergence, compactness, rectifiability,
  and regularity in theorem names.

## 6. Definition and structure names

A public definition names a genuine mathematical object. A public structure names stable reusable
data with laws intrinsic to that object.

Avoid public names ending in `Data`, `Package`, `Context`, `Bundle`, or `Witness` when the
object only shortens binders or carries hypotheses for one proof. Do not package a theorem conclusion
as a structure.

A primed public name is allowed only for a genuinely standard near-variant. A prime must not mean
"new", "fixed", "general version", or an implementation stage.

## 7. Forbidden public-name patterns

Do not expose:

- task history, node identifiers, milestone numbers, or agent terminology;
- effort or status words such as `final`, `complete`, `closure`, `strong`, `clean`,
  `assembly`, `v2`, or `new`;
- proof mechanisms when they are not part of the statement;
- invented abbreviations not standard in GMT or Mathlib;
- misleading classical theorem names for conditional transport or assembly lemmas.

## 8. Source text and review

Non-vendored Lean source contains no comments and no docstrings. Names and signatures must therefore
be honest and searchable. On-disk identifiers are English.

Before accepting a public name, verify:

- the declaration is in its canonical namespace and mathematical home;
- the name matches the exact conclusion and strength;
- every named hypothesis is essential;
- no stronger or more canonical existing declaration was missed;
- special cases are corollaries of the natural theorem;
- normalization and dimension distinctions are visible when mathematically necessary;
- the name contains no task history or implementation route;
- a classical name is used only for the actual classical statement.
