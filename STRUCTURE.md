# STRUCTURE.md - mathematical file and folder placement

This file is the authority for placement, granularity, and dependency structure in `GMT`.
`NAMING.md` governs declaration names. `AGENTS.md` governs workflow, soundness, source discipline,
and delivery.

## 1. Library architecture

Reusable Euclidean geometric measure theory is the product. Regularity theorems and applications are
assembled over shared measure, linear, analytic, rectifiability, varifold, and current foundations.

The canonical top-level pillars are:

```text
GMT/
  Measure/
  Linear/
  Area/
  Rectifiable/
  BV/
  Varifold/
  Current/
  Analysis/
  Regularity/
  External/
```

- `Measure/` contains Hausdorff-measure interfaces, density ratios, differentiation, blow-ups,
  locally finite measures, and measure convergence specific to GMT.
- `Linear/` contains Grassmannians, planes, orthogonal projections, simple multivectors,
  orientations, comass, and linear Jacobian infrastructure not already in Mathlib.
- `Area/` contains tangential Jacobians, multiplicity, area and coarea, Sard-type consequences,
  and parameterization results.
- `Rectifiable/` contains rectifiable sets and measures, approximate tangent planes, tangential
  differentiation, and structure theorems.
- `BV/` contains distributional BV, variation measures, finite-perimeter sets, reduced boundaries,
  Gauss-Green, compactness, lower semicontinuity, and De Giorgi structure.
- `Varifold/` contains general varifolds, weight measures, pushforwards, convergence, rectifiable
  and integral specializations, first variation, generalized mean curvature, and stationarity.
- `Current/` contains test forms, currents, mass, boundary, restriction, pushforward, slicing,
  deformation, flat convergence, compactness, and area minimization.
- `Analysis/` contains dry reusable estimates and constructions needed by several GMT theories:
  approximation, compactness, Sobolev and Poincare inequalities, harmonic analysis, iteration,
  excess decay, and elliptic estimates.
- `Regularity/` contains Allard regularity, minimizing-current regularity, tangent-cone and
  singular-set arguments, and stable-cone results.
- `External/` contains vendored third-party mathematics with provenance and licenses preserved.

Do not create another top-level pillar until its first real reusable declaration exists and its
dependency direction is understood.

## 2. Euclidean scope

The foundational ambient spaces are finite-dimensional real normed or inner-product spaces, with
inner products required only when orthogonal planes, Jacobians, or Euclidean density constants need
them. Prefer intrinsic formulations over hard-coded coordinate spaces.

Coordinate representations, matrices, standard Euclidean spaces, graphs, and classical subsets of
`Fin n -> Real` are specializations and computational interfaces. They do not replace the natural
finite-dimensional theorem.

Riemannian-manifold GMT, chart transport, Riemannian varifolds, manifold currents, and geometric-flow
applications belong in downstream DifferentialGeometry. This repository may expose the Euclidean
theorems needed by that bridge, but must not import DifferentialGeometry.

## 3. Dependency direction

Lean's acyclic module graph is a hard constraint. Maintain this semantic order:

```text
Mathlib
  |
  +-- Measure and Linear
          |
          +-- Area
                |
                +-- Rectifiable
                |      |
                |      +-- Varifold
                |      +-- Current
                |
                +-- BV

Analysis combines only with the lowest layer it genuinely needs.
Regularity consumes Varifold, Current, BV, and Analysis as appropriate.
```

More specifically:

- `Measure/` and `Linear/` remain low-level and independent of varifolds and currents.
- `Area/` may consume `Measure/` and `Linear/`.
- `Rectifiable/` may consume `Area/`; foundational area theory does not import rectifiability.
- `BV/` may consume measure and area foundations. Its general theory does not import currents.
- General varifold definitions precede rectifiable and integral varifold specializations.
- `Varifold/` and `Current/` share lower foundations but do not import each other merely for
  convenience.
- Dry `Analysis/` must not import a geometric object when its theorem can be stated independently.
- `Regularity/` is high-level and may consume all relevant reusable lower layers.
- `External/` may be imported but is not modified to repair local architecture.

Use precise leaf imports. Do not import the flat root aggregate from library source.

## 4. Measure normalization

Use Mathlib's `Measure.euclideanHausdorffMeasure` and notation `μHE` as the canonical normalized
Euclidean Hausdorff measure unless an exact theorem requires the explicit diameter-cover
normalization used in a source.

The bridge between `μHE`, unnormalized `μH`, and any explicit `omega_m / 2^m` scaling belongs
in `Measure/`. Prove it once and reuse it. Density ratios, monotonicity, mass ratios, and Allard
smallness conditions may not introduce private competing normalization conventions.

## 5. General and rectifiable objects

General objects are primary when the operations and weak convergence theory are naturally defined
for them:

- a general varifold is a locally finite measure on ambient space times the Grassmannian;
- rectifiable and integral varifolds are represented specializations;
- a general current is a continuous functional on compactly supported smooth test forms;
- rectifiable and integral currents are represented specializations.

Pedagogical development through a special case does not reverse the final public dependency. Smooth
submanifolds and Lipschitz graphs are constructors, examples, and compatibility theorems.

## 6. Files and concept folders

Placement is mathematical, not line-count driven.

- One coherent development, however long, is one file.
- A single definition with its immediate constructors, simp lemmas, and elementary properties may
  remain in one file.
- A definition with a reusable API and several separable developments becomes a concept folder,
  normally with `Defs.lean`, `Basic.lean`, and mathematically named aspect files.
- Split only at genuine interfaces: definition versus representation, linear versus nonlinear,
  general versus rectifiable, weak compactness versus regularity, or geometric estimate versus
  iteration.
- Never split a proof or create files merely to satisfy a line-count target.
- Private lemmas used by one coherent proof remain with that proof.
- Promote reusable helpers to their natural home; otherwise keep them private.

Files use UpperCamelCase mathematical names. `Defs.lean` and `Basic.lean` are reserved for genuine
concept-folder roles, not generic dumping grounds.

## 7. Suggested subject homes

Create these folders only when the first real declaration lands:

```text
Measure/
  Hausdorff/
  Density/
  Blowup/
  Convergence/

Linear/
  Grassmannian/
  Multivector/
  Comass/

Area/
  Jacobian/
  Multiplicity/
  Coarea/

Rectifiable/
  ApproxTangent/
  TangentialDerivative/

BV/
  FinitePerimeter/
  ReducedBoundary/

Varifold/
  FirstVariation/
  Monotonicity/
  Compactness/

Current/
  TestForm/
  Rectifiable/
  Slicing/
  Deformation/
  Compactness/
  Minimizing/

Regularity/
  Allard/
  TangentCone/
  SingularSet/
  StableCone/
```

The list is a routing guide, not a request to create empty speculative directories.

## 8. Aggregation and namespaces

`GMT.lean` is the single flat root aggregate and imports every public leaf module. There are no
per-folder aggregator modules.

Folders are for mathematical navigation and dependency boundaries. Namespaces follow mathematical
objects and subjects and need not mirror the entire path. Moving a file does not by itself justify
namespace churn.

Every new public leaf is registered in `GMT.lean` and verified by the root build even when it has
no current consumers.

## 9. Variants and theorem direction

Organize variants by their conclusions:

- Different conclusions are coequal siblings over shared foundations.
- The same conclusion with stronger assumptions or a special object is a corollary of the natural
  primary theorem.
- Linear, smooth, Lipschitz, rectifiable, and measure-theoretic versions share the strongest common
  lower foundation but remain distinct when their conclusions differ.
- Local and global results remain separate when globalization requires compactness, local finiteness,
  exhaustion, or gluing.
- Pointwise, almost-everywhere, integrated, and weak formulations are distinct interfaces.

## 10. Placement review

Before accepting a new or moved module, verify:

- the declarations have one canonical mathematical home;
- generic helpers are private or promoted;
- the chosen split reflects a real interface rather than file length;
- imports are precise and acyclic;
- the Euclidean core does not import DifferentialGeometry;
- general objects precede represented specializations;
- analytic estimates are not hidden inside one regularity application;
- normalization is shared rather than redefined;
- the leaf is registered in the flat root aggregate.
