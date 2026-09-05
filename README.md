# GMT

A Lean 4 and Mathlib library for Euclidean geometric measure theory. The current prototype develops
general varifolds, first variation, stationarity, and the stationary monotonicity and density theory.
The intended scope also includes area and coarea, rectifiability, BV and finite perimeter, currents,
and regularity theory.

The project uses Lean and Mathlib version `v4.33.1`.

## Build

```bash
lake exe cache get
lake build GMT
```

## Simon correspondence

The tables below record public declarations corresponding to Leon Simon's *Introduction to
Geometric Measure Theory* (2014 revision). Source links open the Lean statements. Rows explicitly
marked as reparameterizations or derived checks are not presented as literal statements from the
book.

The Chapter 4 monotonicity and density results are proved here for general varifolds in arbitrary
finite-dimensional real inner product spaces. Those results are mathematically more general than
Simon's rectifiable Euclidean formulation. The future rectifiable-varifold representation layer will
provide the formal specialization to Simon's `v(M, theta)` notation; that bridge is not claimed as
completed here.

### Chapter 1: Preliminary measure theory

| Simon | Lean statements |
| --- | --- |
| Normalized Hausdorff measure and the unit-ball constant, Section 2, pp. 9-13 | [`MeasureTheory.euclideanUnitBallVolume`](GMT/Measure/Density.lean#L14), [`MeasureTheory.euclideanHausdorffMeasure_closedBall`](GMT/Measure/Density.lean#L45) |
| Lower and upper densities (3.1) with `A = X`, p. 13 | [`MeasureTheory.Measure.densityRatio`](GMT/Measure/Density.lean#L93), [`MeasureTheory.Measure.lowerDensity`](GMT/Measure/Density.lean#L97), [`MeasureTheory.Measure.upperDensity`](GMT/Measure/Density.lean#L101) |

### Chapter 2: Area and coarea foundations

The reusable Jacobian and linear/product-measure interfaces are recorded in
[`AREA_ACCEPTANCE.md`](AREA_ACCEPTANCE.md). The completed declarations include the scalar
Lipschitz extension theorem, the Mathlib Rademacher interface, the generic Lusin closed-set
continuity theorem and closed differentiability set with continuous derivative used by the C1
approximation proof, the Hausdorff image and fiber estimates, the intrinsic rectangular Jacobian,
the linear area formula, the rectangular injective and general non-injective weighted area
formulas, fiber multiplicity, the finite and countable injective-partition engines, the linear and
general nonlinear coarea formulas, and the `C¹` Sard-type fiber decomposition. The Lipschitz
coarea estimate is available both with the sharp normalized `μHE` coefficient and with Simon's
printed unit-ball-volume ratio. Its public map is globally Lipschitz on the ambient space; Simon's
Theorem 1.9 assumes Lipschitz continuity only on the measured set.

### Chapter 4: Rectifiable n-varifolds

| Simon | Lean statements |
| --- | --- |
| Radial test field and pointwise tangential-divergence formula (3.2), pp. 89-90 | [`radialVectorField`](GMT/Analysis/Radial.lean#L9), [`hasFDerivAt_radialVectorField`](GMT/Analysis/Radial.lean#L30), [`Grassmannian.tangentialTrace_fderiv_radialVectorField`](GMT/Analysis/Radial.lean#L113), [`Grassmannian.tangentialTrace_fderiv_radialVectorField_eq_perpendicularProjection`](GMT/Analysis/Radial.lean#L125), [`Grassmannian.tangentialDivergence_radialVectorField`](GMT/Varifold/FirstVariation.lean#L20), [`Grassmannian.tangentialDivergence_radialVectorField_eq_perpendicularProjection`](GMT/Varifold/FirstVariation.lean#L29) |
| Squared-radius reparameterization used for (3.2)-(3.3), pp. 89-90 | [`squaredRadiusRadialVectorField`](GMT/Analysis/Radial.lean#L14), [`contDiff_squaredRadiusRadialVectorField`](GMT/Analysis/Radial.lean#L20), [`hasFDerivAt_squaredRadiusRadialVectorField`](GMT/Analysis/Radial.lean#L79), [`Grassmannian.tangentialTrace_fderiv_squaredRadiusRadialVectorField`](GMT/Analysis/Radial.lean#L163), [`Grassmannian.tangentialDivergence_squaredRadiusRadialVectorField`](GMT/Varifold/FirstVariation.lean#L40), [`Varifold.IsStationaryOn.integral_squaredRadiusRadial_eq_zero`](GMT/Varifold/Monotonicity.lean#L57), [`Varifold.IsStationaryOn.integral_squaredRadiusRadial_perpendicular_eq_zero`](GMT/Varifold/Monotonicity.lean#L101) |
| Perpendicular radial component and the integrand in (3.6) and (3.10), pp. 90-91 | [`Grassmannian.perpendicularProjection`](GMT/Linear/Grassmannian/Defs.lean#L46), [`Grassmannian.radialTilt`](GMT/Varifold/Monotonicity.lean#L19) |
| Exact stationary monotonicity identity (3.6), p. 90 | [`Varifold.IsStationaryOn.monotonicity`](GMT/Varifold/Monotonicity.lean#L1135), [`Varifold.IsStationaryOn.monotonicity_sub`](GMT/Varifold/Monotonicity.lean#L1153) |
| Mass ratio and normalized density ratio (3.8)-(3.9), p. 91 | [`MeasureTheory.euclideanUnitBallVolume`](GMT/Measure/Density.lean#L14), [`MeasureTheory.Measure.massRatio`](GMT/Measure/Density.lean#L89), [`MeasureTheory.Measure.densityRatio`](GMT/Measure/Density.lean#L93) |
| Monotonicity and existence and finiteness of density (3.8)-(3.9), p. 91 | [`Varifold.IsStationaryOn.massRatio_monotoneOn`](GMT/Varifold/Monotonicity.lean#L1169), [`Varifold.IsStationaryOn.densityRatio_monotoneOn`](GMT/Varifold/Monotonicity.lean#L1180), [`Varifold.IsStationaryOn.tendsto_densityRatio`](GMT/Varifold/Monotonicity.lean#L1189), [`Varifold.IsStationaryOn.lowerDensity_ne_top`](GMT/Varifold/Monotonicity.lean#L1206), [`Varifold.IsStationaryOn.lowerDensity_eq_upperDensity`](GMT/Varifold/Monotonicity.lean#L1229), [`Varifold.IsStationaryOn.upperDensity_ne_top`](GMT/Varifold/Monotonicity.lean#L1237) |
| Density-excess identity (3.10), p. 91 | [`Varifold.IsStationaryOn.density_excess`](GMT/Varifold/Monotonicity.lean#L1245), [`Varifold.IsStationaryOn.density_excess_sub`](GMT/Varifold/Monotonicity.lean#L1346) |
| Upper semicontinuity of stationary density (3.11), p. 91 | [`Varifold.IsStationaryOn.upperSemicontinuousOn_lowerDensity`](GMT/Varifold/Monotonicity.lean#L1358) |

### Chapter 8: Theory of general varifolds

| Simon | Lean statements |
| --- | --- |
| Section 1, Grassmannian and orthogonal projection, p. 205 | [`Grassmannian`](GMT/Linear/Grassmannian/Defs.lean#L8), [`Grassmannian.projection`](GMT/Linear/Grassmannian/Defs.lean#L31), [`Grassmannian.subspace`](GMT/Linear/Grassmannian/Defs.lean#L43) |
| Section 1, general varifold, weight, and mass, pp. 205-206 | [`Varifold`](GMT/Varifold/Defs.lean#L9), [`Varifold.weightMeasure`](GMT/Varifold/Defs.lean#L67), [`Varifold.mass`](GMT/Varifold/Defs.lean#L70), [`Varifold.massOn`](GMT/Varifold/Defs.lean#L73) |
| Section 1, restriction, p. 206 | [`Varifold.restrict`](GMT/Varifold/Basic.lean#L45), [`Varifold.toMeasure_restrict`](GMT/Varifold/Basic.lean#L49), [`Varifold.weightMeasure_restrict`](GMT/Varifold/Basic.lean#L52) |
| Section 1, multiplicity-one plane `v(T)`, p. 206 | [`Varifold.ofPlane`](GMT/Varifold/Plane.lean#L48), [`Varifold.toMeasure_ofPlane`](GMT/Varifold/Plane.lean#L61), [`Varifold.weightMeasure_ofPlane`](GMT/Varifold/Plane.lean#L85) |
| Section 2, first-variation integral (2.3) and tangential divergence (2.4), p. 209 | [`Grassmannian.tangentialDivergence`](GMT/Varifold/FirstVariation.lean#L16), [`Varifold.firstVariation`](GMT/Varifold/FirstVariation.lean#L162), [`Varifold.firstVariation_apply`](GMT/Varifold/FirstVariation.lean#L177), [`Varifold.firstVariation_apply_restrict`](GMT/Varifold/FirstVariation.lean#L184) |
| Section 2, unnumbered stationarity definition following (2.4), p. 209 | [`Varifold.IsStationaryOn`](GMT/Varifold/FirstVariation.lean#L225), [`Varifold.IsStationaryOn.integral_tangentialDivergence_eq_zero`](GMT/Varifold/FirstVariation.lean#L250), [`Varifold.IsStationaryOn.integral_tangentialDivergence_eq_zero_restrict`](GMT/Varifold/FirstVariation.lean#L258) |
| Section 3, perpendicular radial term in (3.2)-(3.4), pp. 210-211 | [`Grassmannian.perpendicularProjection`](GMT/Linear/Grassmannian/Defs.lean#L46), [`Grassmannian.radialTilt`](GMT/Varifold/Monotonicity.lean#L19) |
| Section 3, stationary case of (3.3), p. 210, with the exact two-radius identity from Chapter 4 (3.6) | [`Varifold.IsStationaryOn.monotonicity`](GMT/Varifold/Monotonicity.lean#L1135), [`Varifold.IsStationaryOn.monotonicity_sub`](GMT/Varifold/Monotonicity.lean#L1153), [`Varifold.IsStationaryOn.massRatio_monotoneOn`](GMT/Varifold/Monotonicity.lean#L1169), [`Varifold.IsStationaryOn.densityRatio_monotoneOn`](GMT/Varifold/Monotonicity.lean#L1180), [`Varifold.IsStationaryOn.tendsto_densityRatio`](GMT/Varifold/Monotonicity.lean#L1189) |
| Section 3, exact stationary density-excess identity (3.4), p. 211 | [`Varifold.IsStationaryOn.density_excess`](GMT/Varifold/Monotonicity.lean#L1245), [`Varifold.IsStationaryOn.density_excess_sub`](GMT/Varifold/Monotonicity.lean#L1346) |
| Derived flat-plane and normalization checks | [`Varifold.radialTilt_ae_eq_zero_ofPlane`](GMT/Varifold/Plane.lean#L64), [`Varifold.setLIntegral_radialTilt_ofPlane`](GMT/Varifold/Plane.lean#L76), [`Varifold.weightMeasure_ofPlane_closedBall`](GMT/Varifold/Plane.lean#L98), [`Varifold.massRatio_ofPlane`](GMT/Varifold/Plane.lean#L116), [`Varifold.densityRatio_ofPlane`](GMT/Varifold/Plane.lean#L124), [`Varifold.isStationaryOn_ofPlane`](GMT/Varifold/Plane.lean#L132), [`Varifold.lowerDensity_ofPlane`](GMT/Varifold/Plane.lean#L196), [`Varifold.upperDensity_ofPlane`](GMT/Varifold/Plane.lean#L209), [`Varifold.ofPlane_ne_zero`](GMT/Varifold/Plane.lean#L216) |

Lean represents a plane intrinsically by its self-adjoint idempotent projection with trace `n`.
The inherited operator-norm metric is not Simon's displayed Hilbert-Schmidt metric, but the two
metrics induce the same topology and Borel structure in finite dimensions; no literal equality of
those metric values is claimed.

Beyond the Chapter 1 normalization and density interfaces listed above, Chapters 1-3 and 5-7 do not
yet have chapter-level public formalizations in this repository. Chapter 8's rectifiability theorem,
locally bounded first variation, and nonstationary monotonicity are also not yet formalized. Imported
Mathlib results are not counted as completed GMT coverage.
